# -*- coding: utf-8 -*-
"""
نظام إدارة مخازن ومبيعات قطع غيار مرسيدس - الإصدار 3 (احترافي)
==============================================================
التشغيل محلياً:
    pip install -r requirements.txt
    streamlit run mercedes_parts_app.py

النشر على Streamlit Cloud:
    1) ارفع هذا الملف + requirements.txt على GitHub
    2) (اختياري) من Settings > Secrets:   APP_PASSWORD = "كلمة_المرور_الأولى"
       أو متغير بيئة MERCEDES_APP_PASSWORD. الافتراضي عند أول تشغيل: admin123 (غيّرها فوراً).
ملاحظة: ملفات Streamlit Cloud مؤقتة، لذا خُذ نسخة احتياطية دورياً من صفحة الإعدادات.

ملخص التعديلات في هذا الإصدار (ابحث عن علامة ✅ [تعديل N] في الكود):
  ✅ [تعديل 1] التزامن: كل عملية مالية داخل BEGIN IMMEDIATE (دالة tx)، وأرقام الفواتير/المرتجعات من عدّاد ذري داخل
               نفس المعاملة، وخصم المخزون بـ UPDATE ... WHERE quantity>=? مع فحص rowcount، وقيد CHECK(quantity>=0).
  ✅ [تعديل 2] POS: تصفير كامل (عميل/هاتف/بحث/كمية/خصم يدوي/خصم فاتورة) بعد البيع أو "فاتورة جديدة"،
               وحد الخصم الأقصى يُطبَّق على إجمالي الخصم الفعلي للفاتورة (عروض + يدوي + فاتورة) في الواجهة وفي الخادم.
  ✅ [تعديل 3] المرتجعات في جدول returns مستقل (تاريخ/فرع/سبب/مبلغ) ولا تُعدَّل الفاتورة الأصلية إطلاقاً؛
               كل التقارير تُحسب من view باسم v_movements (مبيعات − مرتجعات بتاريخ كل منهما).
  ✅ [تعديل 4] البيانات التجريبية اختيارية عند أول تشغيل، مع حذفها/تصفير النظام من الإعدادات، وملف requirements.txt مثبّت.
  ✅ [تعديل 5] رقم OEM لم يعد UNIQUE وحده: التفرّد على (OEM + الماركة + المنشأ + الفرع) بدون لواحق وهمية.
               قواعد البيانات القديمة تُرقّى تلقائياً (إعادة بناء الجدول وإزالة اللواحق القديمة).
  ✅ [تعديل 6] بحث يتجاهل الهمزات (أ إ آ→ا) و(ة→ه) و(ى→ي) والتشكيل والمسافات الزائدة والأرقام الهندية،
               وقفل الدخول بعد المحاولات الخاطئة صار على مستوى السيرفر (مخزَّن في قاعدة البيانات) بمهلة متصاعدة.
محفوظ كما هو: PBKDF2+salt، الاستعلامات المعلّمة (Parameterized)، html.escape، التراجع (Rollback)،
منطق أفضل عرض للعميل، باركود EAN-13، وتصميم RTL العربي.
"""
import os, re, json, sqlite3, random, html, hmac, hashlib, secrets, time, datetime, urllib.parse, tempfile, contextlib
from pathlib import Path
import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

DB = str(Path(__file__).with_name("mercedes_parts.db"))
SCHEMA_VERSION = "3"
BRANCHES = ["الفرع الرئيسي", "فرع الإسكندرية", "فرع الجيزة", "فرع طنطا"]
ORIGINS = ["أصلي ألماني Original Germany", "بديل ألماني German Aftermarket", "تايواني Taiwan", "صيني China"]
SEARCH_COLS = ["part_number", "name", "category", "model", "brand", "quality_origin", "location", "barcode"]
INV_COLS = "id, part_number, name, category, model, brand, quality_origin, quantity, cost_price, selling_price, branch, location, barcode"
LETTER = {"تيل فرامل": "A", "فرامل": "A", "فلاتر": "B", "طرمبات": "C", "كهرباء": "D", "عفشة": "E", "محرك": "F", "زيوت": "G"}
AR = {"id": "م", "part_number": "رقم OEM", "name": "اسم القطعة", "category": "الفئة", "model": "الموديل",
      "brand": "الماركة", "quality_origin": "المنشأ/الجودة", "quantity": "الكمية", "cost_price": "سعر التكلفة",
      "selling_price": "سعر البيع", "branch": "الفرع", "location": "مكان التخزين", "barcode": "الباركود"}
PERIODS = ["كل الفترة", "اليوم", "آخر 7 أيام", "آخر 30 يوم"]
SCOPES = ["كل الأصناف", "فئة", "ماركة", "منشأ/جودة", "موديل", "رقم OEM"]
OFFER_TYPES = ["نسبة %", "مبلغ ثابت للقطعة"]
SCAN_LABEL = "📷 امسح الباركود هنا ثم Enter"
RETURN_REASONS = ["عيب في القطعة", "قطعة غير مطابقة للسيارة", "تغيير رأي العميل", "خطأ في الفاتورة", "أخرى"]
# مفتاح "المنتج" = نفس رقم OEM + الماركة + المنشأ (باركود واحد لكل الفروع)
VARIANT_SQL = "part_number=? COLLATE NOCASE AND brand=? COLLATE NOCASE AND quality_origin=?"
LOCK_AFTER, LOCK_BASE, LOCK_MAX = 5, 30, 900  # قفل الدخول: بعد 5 محاولات، 30ث تتضاعف حتى 15 دقيقة

# ============================================================== ✅ [تعديل 6] تطبيع النص العربي للبحث
_TASHKEEL = re.compile("[\u064b-\u065f\u0670\u0640]")  # التشكيل + التطويل
_NORM_MAP = str.maketrans({"أ": "ا", "إ": "ا", "آ": "ا", "ٱ": "ا", "ة": "ه", "ى": "ي",
                           **{chr(0x0660 + i): str(i) for i in range(10)},      # أرقام هندية ٠-٩
                           **{chr(0x06F0 + i): str(i) for i in range(10)}})     # أرقام فارسية

def norm_text(s):
    """يوحّد الهمزات والتاء المربوطة والألف المقصورة ويحذف التشكيل ويضغط المسافات ويحوّل لحروف صغيرة."""
    s = _TASHKEEL.sub("", str(s if s is not None else ""))
    return " ".join(s.translate(_NORM_MAP).casefold().split())

# ============================================================== قاعدة البيانات
def conn():
    # isolation_level=None: نتحكم بالمعاملات يدوياً (BEGIN IMMEDIATE) — ✅ [تعديل 1]
    c = sqlite3.connect(DB, timeout=30, isolation_level=None, check_same_thread=False)
    c.row_factory = sqlite3.Row
    c.create_function("norm", 1, norm_text, deterministic=True)  # يُستعمل داخل SQL للبحث المطبَّع
    try:
        c.execute("PRAGMA busy_timeout=30000")
        c.execute("PRAGMA journal_mode=WAL")  # قراءة وكتابة متزامنة أفضل
        c.execute("PRAGMA synchronous=NORMAL")
    except sqlite3.OperationalError:
        pass
    return c

def qdf(sql, p=()):
    c = conn()
    try:
        return pd.read_sql_query(sql, c, params=list(p))
    finally:
        c.close()

def run(sql, p=()):
    c = conn()
    try:
        c.execute(sql, p)
    finally:
        c.close()

@contextlib.contextmanager
def tx():
    """✅ [تعديل 1] معاملة كتابة: BEGIN IMMEDIATE يحجز قفل الكتابة فوراً فتتسلسل العمليات المتزامنة،
    وأي استثناء يؤدي إلى ROLLBACK كامل (لا يبقى نصف فاتورة ولا يُستهلك رقم)."""
    c = conn()
    try:
        c.execute("BEGIN IMMEDIATE")
        yield c
        c.execute("COMMIT")
    except BaseException:
        try:
            c.execute("ROLLBACK")
        except sqlite3.Error:
            pass
        raise
    finally:
        c.close()

def _get(c, k, d=""):
    r = c.execute("SELECT value FROM settings WHERE key=?", (k,)).fetchone()
    return r["value"] if r else d

def _set(c, k, v):
    c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (k, str(v)))

def get_setting(k, d=""):
    r = qdf("SELECT value FROM settings WHERE key=?", (k,))
    return r.iloc[0, 0] if not r.empty else d

def set_setting(k, v):
    with tx() as c:
        _set(c, k, v)

def next_seq(c, key):
    """✅ [تعديل 1] عدّاد تسلسلي ذري (يُستدعى داخل tx فقط) → لا يتكرر رقم فاتورة/مرتجع أبداً."""
    n = int(_get(c, key, "0") or 0) + 1
    _set(c, key, n)
    return n

def low_limit():
    try:
        return max(1, int(get_setting("low_limit", "10")))
    except ValueError:
        return 10

def max_discount():
    try:
        return float(get_setting("max_discount", "30"))
    except ValueError:
        return 30.0

# --- كلمة المرور (PBKDF2 + salt) وقفل الدخول على مستوى السيرفر
def hash_pw(pw, salt_hex):
    return hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), bytes.fromhex(salt_hex), 150000).hex()

def set_password(pw, default=False):
    salt = secrets.token_hex(16)
    with tx() as c:
        _set(c, "pw_salt", salt); _set(c, "pw_hash", hash_pw(pw, salt)); _set(c, "pw_default", "1" if default else "0")

def login_attempt(pw):
    """✅ [تعديل 6] يتحقق من كلمة المرور ويطبّق القفل المخزَّن في قاعدة البيانات (عام لكل الجلسات).
    يرجع (نجح؟, ثواني الانتظار). المحاولات الخاطئة تُحسب داخل معاملة واحدة فلا يمكن تجاوزها بتعدد الجلسات."""
    with tx() as c:
        now = time.time()
        lock_until = float(_get(c, "lock_until", "0") or 0)
        if now < lock_until:
            return False, int(lock_until - now) + 1
        salt, h = _get(c, "pw_salt"), _get(c, "pw_hash")
        if salt and h and hmac.compare_digest(hash_pw(pw, salt), h):
            _set(c, "fail_count", 0); _set(c, "lock_until", 0)
            return True, 0
        fails = int(_get(c, "fail_count", "0") or 0) + 1
        _set(c, "fail_count", fails)
        wait = 0
        if fails >= LOCK_AFTER:
            wait = min(LOCK_MAX, LOCK_BASE * 2 ** (fails - LOCK_AFTER))
            _set(c, "lock_until", now + wait)
        return False, wait

def initial_password():
    p = os.environ.get("MERCEDES_APP_PASSWORD")
    if p:
        return p, False
    try:
        return str(st.secrets["APP_PASSWORD"]), False
    except Exception:
        return "admin123", True

# ============================================================== هيكل الجداول
# ✅ [تعديل 5] لا يوجد UNIQUE على part_number وحده؛ التفرّد في الفهرس uq_inventory_variant بالأسفل.
INVENTORY_DDL = """CREATE TABLE IF NOT EXISTS {name}(
    id INTEGER PRIMARY KEY AUTOINCREMENT, part_number TEXT NOT NULL, name TEXT, category TEXT, model TEXT,
    brand TEXT NOT NULL DEFAULT '', quality_origin TEXT NOT NULL DEFAULT '', quantity INTEGER NOT NULL DEFAULT 0 CHECK(quantity>=0),
    cost_price REAL, selling_price REAL, branch TEXT NOT NULL, location TEXT DEFAULT '', barcode TEXT DEFAULT '',
    is_demo INTEGER DEFAULT 0)"""
INVOICES_DDL = """CREATE TABLE IF NOT EXISTS invoices(
    id INTEGER PRIMARY KEY AUTOINCREMENT, invoice_no TEXT, date TEXT, customer TEXT, customer_phone TEXT DEFAULT '',
    branch TEXT, inventory_id INTEGER, part_number TEXT, name TEXT, model TEXT, brand TEXT, quality_origin TEXT,
    qty INTEGER, unit_price REAL, total REAL, unit_cost REAL DEFAULT 0, list_price REAL DEFAULT 0, discount_note TEXT DEFAULT '')"""
# ✅ [تعديل 3] جدول مستقل للمرتجعات (الفاتورة الأصلية لا تتغير أبداً)
RETURNS_DDL = """CREATE TABLE IF NOT EXISTS returns(
    id INTEGER PRIMARY KEY AUTOINCREMENT, return_no TEXT, date TEXT, invoice_no TEXT, invoice_line_id INTEGER,
    inventory_id INTEGER, branch TEXT, part_number TEXT, name TEXT, model TEXT, brand TEXT, quality_origin TEXT,
    qty INTEGER NOT NULL CHECK(qty>0), unit_price REAL, unit_cost REAL DEFAULT 0, list_price REAL DEFAULT 0,
    amount REAL, reason TEXT DEFAULT '', customer TEXT DEFAULT '')"""
TRANSFERS_DDL = """CREATE TABLE IF NOT EXISTS transfers(
    id INTEGER PRIMARY KEY AUTOINCREMENT, date TEXT, part_number TEXT, name TEXT, brand TEXT,
    quality_origin TEXT, from_branch TEXT, to_branch TEXT, qty INTEGER)"""
OFFERS_DDL = """CREATE TABLE IF NOT EXISTS offers(
    id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, type TEXT, value REAL, scope TEXT, scope_value TEXT DEFAULT '',
    branch TEXT DEFAULT 'الكل', min_qty INTEGER DEFAULT 1, start_date TEXT DEFAULT '', end_date TEXT DEFAULT '',
    active INTEGER DEFAULT 1)"""
# ✅ [تعديل 3] كل التقارير تقرأ من هذا الـ VIEW: المبيعات موجبة بتاريخ الفاتورة، والمرتجعات سالبة بتاريخ المرتجع
MOVEMENTS_VIEW = """CREATE VIEW v_movements AS
    SELECT 'sale' AS kind, date, branch, invoice_no, name, model, brand, quality_origin, qty,
           qty*unit_price AS amount, qty*(unit_price-COALESCE(unit_cost,0)) AS profit,
           qty*(COALESCE(NULLIF(list_price,0),unit_price)-unit_price) AS disc
    FROM invoices
    UNION ALL
    SELECT 'return', date, branch, invoice_no, name, model, brand, quality_origin, -qty,
           -amount, -(qty*(unit_price-COALESCE(unit_cost,0))), -(qty*(COALESCE(NULLIF(list_price,0),unit_price)-unit_price))
    FROM returns"""

# ============================================================== البيانات التجريبية (اختيارية) ✅ [تعديل 4]
PART_TYPES = [
    ("تيل فرامل أمامي Front Brake Pads", "تيل فرامل", "420", 3800, "Bosch"),
    ("تيل فرامل خلفي Rear Brake Pads", "تيل فرامل", "423", 3200, "Bosch"),
    ("هوب فرامل أمامي Front Brake Disc", "فرامل", "421", 5200, "Febi"),
    ("فلتر زيت Oil Filter", "فلاتر", "180", 650, "Bosch"),
    ("فلتر هواء Air Filter", "فلاتر", "094", 900, "Bosch"),
    ("فلتر مكيف Cabin Filter", "فلاتر", "830", 700, "Bosch"),
    ("طرمبة بنزين Fuel Pump", "طرمبات", "470", 6500, "Bosch"),
    ("طرمبة مياه Water Pump", "طرمبات", "200", 4800, "Febi"),
    ("طقم شمعات اشتعال Spark Plugs Set", "كهرباء", "159", 2400, "Bosch"),
    ("مساعد أمامي Front Shock Absorber", "عفشة", "320", 7800, "Febi"),
    ("مقص أمامي Front Control Arm", "عفشة", "330", 4200, "Febi"),
    ("كرسي موتور Engine Mount", "محرك", "240", 2900, "Febi"),
    ("ثرموستات Thermostat", "محرك", "203", 1700, "Febi"),
    ("زيت محرك 5W-30 (4 لتر) Engine Oil", "زيوت", "989", 2300, "Febi"),
    ("بوبينة اشتعال Ignition Coil", "كهرباء", "150", 1800, "Bosch"),
]
MODELS = [("C-Class W204", "204", 0.90), ("C-Class W205", "205", 1.00), ("E-Class W212", "212", 1.05),
          ("E-Class W213", "213", 1.20), ("GLC X253", "253", 1.25)]

def seed(c):
    """يدرج 300 صنف تجريبي (15 نوع × 5 موديلات × 4 جودات). لاحظ: نفس رقم OEM للجودات الأربع بدون لواحق ✅ [تعديل 5]."""
    rng = random.Random(2024)
    rows = []
    for t, (tname, cat, grp, cost, de) in enumerate(PART_TYPES):
        for m, (model, chs, mm) in enumerate(MODELS):
            branch = BRANCHES[(t * len(MODELS) + m) % 4]
            oem = f"A{chs}{grp}{rng.choice(['00','01','02','03','04'])}{rng.choice(['00','10','20','28','31','32','37'])}"
            shelf = rng.randint(1, 20)
            variants = [("Mercedes-Benz", ORIGINS[0], 1.00, 1.30), (de, ORIGINS[1], 0.68, 1.35),
                        ("TW-Auto", ORIGINS[2], 0.42, 1.45), ("CN-Auto", ORIGINS[3], 0.27, 1.55)]
            for vi, (brand, origin, vm, margin) in enumerate(variants):
                cp = round(cost * mm * vm / 5) * 5
                sp = round(cp * margin / 5) * 5
                qty = rng.randint(0, 9) if rng.random() < 0.15 else rng.randint(10, 80)
                rows.append((oem, tname, cat, model, brand, origin, qty, cp, sp, branch,
                             f"{LETTER.get(cat, 'H')}-{shelf:02d}-{vi + 1}", 1))
    c.executemany("INSERT OR IGNORE INTO inventory(part_number,name,category,model,brand,quality_origin,quantity,cost_price,"
                  "selling_price,branch,location,is_demo) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)", rows)
    return len(rows)

def load_demo():
    with tx() as c:
        n = seed(c)
        fill_barcodes(c)
        _set(c, "setup_done", "1")
    return n

def purge_demo_items():
    """يحذف الأصناف التجريبية التي لم تُستخدم في أي فاتورة. يرجع (المحذوف, المتبقي لارتباطه بفواتير)."""
    with tx() as c:
        used = {r[0] for r in c.execute("SELECT DISTINCT inventory_id FROM invoices")}
        ids = [r[0] for r in c.execute("SELECT id FROM inventory WHERE is_demo=1")]
        gone = [i for i in ids if i not in used]
        c.executemany("DELETE FROM inventory WHERE id=?", [(i,) for i in gone])
    return len(gone), len(ids) - len(gone)

def reset_operations():
    """يمسح الفواتير والمرتجعات والتحويلات ويصفّر العدّادات (يُبقي المخزون والإعدادات)."""
    with tx() as c:
        for t in ("returns", "invoices", "transfers"):
            c.execute(f"DELETE FROM {t}")
        _set(c, "invoice_seq", 0); _set(c, "return_seq", 0)

def reset_all():
    """تصفير كامل: المخزون والعروض وكل السجلات (يُبقي الإعدادات وكلمة المرور)."""
    reset_operations()
    with tx() as c:
        c.execute("DELETE FROM inventory"); c.execute("DELETE FROM offers")

# ============================================================== الترقية (Migrations) وتهيئة القاعدة
def ensure_col(c, table, col, ddl):
    if col not in [r[1] for r in c.execute(f"PRAGMA table_info({table})")]:
        c.execute(f"ALTER TABLE {table} ADD COLUMN {col} {ddl}")
        return True
    return False

_OLD_SUFFIX = re.compile(r"(?:-(?:BOS|FEB|TW|CN)|/(?:HQ|ALX|GZ|TNT))+$")  # لواحق الإصدارات السابقة

def migrate_inventory(c):
    """✅ [تعديل 5] قاعدة قديمة فيها part_number UNIQUE: نعيد بناء الجدول بدون القيد ونزيل اللواحق الوهمية القديمة."""
    legacy = False
    for ix in c.execute("PRAGMA index_list(inventory)").fetchall():
        if ix["unique"] and [r["name"] for r in c.execute(f"PRAGMA index_info({ix['name']})")] == ["part_number"]:
            legacy = True
    if not legacy:
        return
    c.execute("DROP TABLE IF EXISTS inventory_new")
    c.execute(INVENTORY_DDL.format(name="inventory_new"))
    seen = set()
    for r in c.execute("SELECT * FROM inventory ORDER BY id").fetchall():
        orig = r["part_number"] or f"ID{r['id']}"
        pn = _OLD_SUFFIX.sub("", orig) or orig
        for cand in (pn, orig, f"{orig}#{r['id']}"):          # نتجنّب أي تعارض بعد إزالة اللاحقة
            key = (cand.lower(), (r["brand"] or "").lower(), r["quality_origin"] or "", r["branch"])
            if key not in seen:
                seen.add(key); pn = cand; break
        c.execute("""INSERT INTO inventory_new(id,part_number,name,category,model,brand,quality_origin,quantity,cost_price,
            selling_price,branch,location,barcode,is_demo) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                  (r["id"], pn, r["name"], r["category"], r["model"], r["brand"] or "", r["quality_origin"] or "",
                   max(0, int(r["quantity"] or 0)), r["cost_price"], r["selling_price"], r["branch"] or BRANCHES[0],
                   r["location"] or "", r["barcode"] or "", r["is_demo"] or 0))
    c.execute("DROP TABLE inventory")
    c.execute("ALTER TABLE inventory_new RENAME TO inventory")

def fill_barcodes(c):
    """يعطي كل صنف بلا باركود نفس باركود منتجه في الفروع الأخرى إن وُجد، وإلا باركوداً داخلياً EAN-13."""
    for r in c.execute("SELECT id,part_number,brand,quality_origin FROM inventory WHERE barcode IS NULL OR barcode='' ORDER BY id").fetchall():
        same = c.execute(f"SELECT barcode FROM inventory WHERE {VARIANT_SQL} AND barcode<>'' LIMIT 1",
                         (r["part_number"], r["brand"], r["quality_origin"])).fetchone()
        c.execute("UPDATE inventory SET barcode=? WHERE id=?", (same["barcode"] if same else internal_barcode(r["id"]), r["id"]))

def _init_counter(c, key, table, col):
    if c.execute("SELECT 1 FROM settings WHERE key=?", (key,)).fetchone():
        return
    mx = 0
    for r in c.execute(f"SELECT {col} v FROM {table}").fetchall():
        m = re.search(r"(\d+)$", str(r["v"] or ""))
        mx = max(mx, int(m.group(1)) if m else 0)
    _set(c, key, mx)

def migrate_legacy_returns(c):
    """✅ [تعديل 3] نقل المرتجعات القديمة (returned_qty داخل الفاتورة) إلى جدول returns مرة واحدة فقط."""
    if _get(c, "returns_migrated") == "1":
        return
    if "returned_qty" in [r[1] for r in c.execute("PRAGMA table_info(invoices)")]:
        for r in c.execute("SELECT * FROM invoices WHERE returned_qty>0").fetchall():
            up = r["unit_price"] or 0
            c.execute("""INSERT INTO returns(return_no,date,invoice_no,invoice_line_id,inventory_id,branch,part_number,name,model,
                brand,quality_origin,qty,unit_price,unit_cost,list_price,amount,reason,customer) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                      (f"RET-{next_seq(c, 'return_seq'):06d}", r["date"], r["invoice_no"], r["id"], r["inventory_id"], r["branch"],
                       r["part_number"], r["name"], r["model"], r["brand"], r["quality_origin"], int(r["returned_qty"]), up,
                       r["unit_cost"] or 0, r["list_price"] or up, int(r["returned_qty"]) * up,
                       "ترحيل من النسخة القديمة (تاريخ الفاتورة)", r["customer"]))
    _set(c, "returns_migrated", "1")

def init_db():
    with tx() as c:
        c.execute("CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT)")
        c.execute(INVENTORY_DDL.format(name="inventory"))
        for ddl in (INVOICES_DDL, RETURNS_DDL, TRANSFERS_DDL, OFFERS_DDL):
            c.execute(ddl)
        # أعمدة الإصدارات السابقة
        ensure_col(c, "inventory", "location", "TEXT DEFAULT ''")
        ensure_col(c, "inventory", "barcode", "TEXT DEFAULT ''")
        ensure_col(c, "inventory", "is_demo", "INTEGER DEFAULT 0")
        new_cost = ensure_col(c, "invoices", "unit_cost", "REAL DEFAULT 0")
        ensure_col(c, "invoices", "customer_phone", "TEXT DEFAULT ''")
        ensure_col(c, "invoices", "list_price", "REAL DEFAULT 0")
        ensure_col(c, "invoices", "discount_note", "TEXT DEFAULT ''")
        if new_cost:
            c.execute("UPDATE invoices SET unit_cost=COALESCE((SELECT cost_price FROM inventory WHERE inventory.id=invoices.inventory_id),0)")
        c.execute("UPDATE invoices SET list_price=unit_price WHERE list_price IS NULL OR list_price=0")
        migrate_inventory(c)
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS uq_inventory_variant ON inventory(part_number COLLATE NOCASE, brand COLLATE NOCASE, quality_origin, branch)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_inv_barcode ON inventory(barcode)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_inv_branch ON inventory(branch)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_invoices_no ON invoices(invoice_no)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_returns_line ON returns(invoice_line_id)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_returns_inv ON returns(invoice_no)")
        try:  # شبكة أمان إضافية ضد تكرار بند في نفس الفاتورة
            c.execute("CREATE UNIQUE INDEX IF NOT EXISTS uq_invoice_line ON invoices(invoice_no, inventory_id)")
        except sqlite3.IntegrityError:
            pass
        fill_barcodes(c)
        for r in c.execute("SELECT id,category FROM inventory WHERE location IS NULL OR location=''").fetchall():
            c.execute("UPDATE inventory SET location=? WHERE id=?", (f"{LETTER.get(r['category'], 'H')}-{r['id'] % 20 + 1:02d}-{r['id'] % 4 + 1}", r["id"]))
        _init_counter(c, "invoice_seq", "invoices", "invoice_no")
        _init_counter(c, "return_seq", "returns", "return_no")
        migrate_legacy_returns(c)
        c.execute("DROP VIEW IF EXISTS v_movements")
        c.execute(MOVEMENTS_VIEW)
        for k, v in {"store_name": "قطع غيار مرسيدس", "store_phone": "", "store_address": "", "low_limit": "10",
                     "max_discount": "30", "fail_count": "0", "lock_until": "0"}.items():
            c.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)", (k, v))
        if not c.execute("SELECT 1 FROM settings WHERE key='pw_hash'").fetchone():
            pw, is_default = initial_password()
            salt = secrets.token_hex(16)
            _set(c, "pw_salt", salt); _set(c, "pw_hash", hash_pw(pw, salt)); _set(c, "pw_default", "1" if is_default else "0")
        # ✅ [تعديل 4] لا نحمّل بيانات تجريبية تلقائياً. القواعد التي فيها بيانات فعلية تتخطى شاشة البداية.
        if _get(c, "setup_done") != "1" and (c.execute("SELECT COUNT(*) FROM inventory").fetchone()[0]
                                              or c.execute("SELECT COUNT(*) FROM invoices").fetchone()[0]):
            _set(c, "setup_done", "1")
        _set(c, "schema_version", SCHEMA_VERSION)

def ensure_ready():
    """فحص خفيف في كل تشغيل للصفحة؛ التهيئة/الترقية الكاملة مرة واحدة فقط لكل إصدار هيكل."""
    try:
        if get_setting("schema_version") == SCHEMA_VERSION:
            return
    except Exception:
        pass
    init_db()

# ============================================================== البحث والبيانات
def search_inv(text="", branch=None, brand=None, origin=None):
    """✅ [تعديل 6] بحث مطبَّع: كل كلمة يجب أن توجد في أحد الأعمدة بعد توحيد الهمزات/التاء المربوطة/المسافات.
    INSTR بدل LIKE فلا تتأثر النتيجة بالرمزين % و _ ، والمعلمات دائماً مرتبطة (Parameterized)."""
    sql, p = f"SELECT {INV_COLS} FROM inventory WHERE 1=1", []
    for tok in norm_text(text).split():
        sql += " AND (" + " OR ".join(f"INSTR(norm({c}), ?) > 0" for c in SEARCH_COLS) + ")"
        p += [tok] * len(SEARCH_COLS)
    if branch and branch != "الكل":
        sql += " AND branch=?"; p.append(branch)
    if brand and brand != "الكل":
        sql += " AND brand=?"; p.append(brand)
    if origin and origin != "الكل":
        sql += " AND quality_origin=?"; p.append(origin)
    return qdf(sql + " ORDER BY name, model, selling_price DESC", p)

def show(df):
    return df.rename(columns=AR)

def period_clause(period):
    today = datetime.date.today()
    start = {"اليوم": today, "آخر 7 أيام": today - datetime.timedelta(days=6),
             "آخر 30 يوم": today - datetime.timedelta(days=29)}.get(period)
    return (" AND date>=?", [start.isoformat()]) if start else ("", [])

def branch_clause(branch):
    return ("", []) if branch in (None, "الكل", "كل الفروع") else (" AND branch=?", [branch])

def dashboard_data(period):
    pc, pp = period_clause(period)
    low = low_limit()
    inv = qdf("""SELECT branch, COUNT(*) items, SUM(quantity) pieces, SUM(quantity*selling_price) val_sell,
        SUM(quantity*cost_price) val_cost, SUM(CASE WHEN quantity<? THEN 1 ELSE 0 END) low,
        SUM(CASE WHEN quantity=0 THEN 1 ELSE 0 END) zero FROM inventory GROUP BY branch""", (low,))
    inv = inv.set_index("branch").reindex(BRANCHES).fillna(0).astype(float)
    # ✅ [تعديل 3] المبيعات بتاريخ الفاتورة، والمرتجعات بتاريخ المرتجع نفسه (لا تتغير أرقام الشهور السابقة)
    sal = qdf(f"""SELECT branch,
        SUM(CASE WHEN kind='sale' THEN amount ELSE 0 END) gross,
        SUM(CASE WHEN kind='return' THEN -amount ELSE 0 END) ret,
        SUM(amount) net, SUM(profit) profit,
        SUM(CASE WHEN kind='sale' THEN disc ELSE 0 END) disc,
        COUNT(DISTINCT CASE WHEN kind='sale' THEN invoice_no END) n
        FROM v_movements WHERE 1=1{pc} GROUP BY branch""", pp)
    sal = sal.set_index("branch").reindex(BRANCHES).fillna(0).astype(float)
    daily = qdf(f"SELECT substr(date,1,10) d, SUM(amount) s FROM v_movements WHERE 1=1{pc} GROUP BY d ORDER BY d", pp)
    top = qdf(f"""SELECT name, model, SUM(qty) pieces, SUM(amount) net FROM v_movements WHERE 1=1{pc}
        GROUP BY name, model HAVING pieces>0 ORDER BY pieces DESC LIMIT 8""", pp)
    lows = qdf(f"SELECT {INV_COLS} FROM inventory WHERE quantity<? ORDER BY quantity, branch LIMIT 15", (low,))
    return inv, sal, daily, top, lows

# ============================================================== الباركود EAN-13
EAN_L = ["0001101", "0011001", "0010011", "0111101", "0100011", "0110001", "0101111", "0111011", "0110111", "0001011"]
EAN_PAR = ["LLLLLL", "LLGLGG", "LLGGLG", "LLGGGL", "LGLLGG", "LGGLLG", "LGGGLL", "LGLGLG", "LGLGGL", "LGGLGL"]

def ean_check(d12):
    return str((10 - sum(int(ch) * (3 if i % 2 else 1) for i, ch in enumerate(d12)) % 10) % 10)

def internal_barcode(i):
    d = "20" + f"{int(i):010d}"
    return d + ean_check(d)

def valid_ean13(code):
    code = str(code or "")
    return len(code) == 13 and code.isdigit() and ean_check(code[:12]) == code[12]

def ean13_bits(code):
    par = EAN_PAR[int(code[0])]
    bits = "101"
    for i, ch in enumerate(code[1:7]):
        l = EAN_L[int(ch)]
        r = "".join("1" if b == "0" else "0" for b in l)
        bits += l if par[i] == "L" else r[::-1]
    bits += "01010"
    for ch in code[7:13]:
        bits += "".join("1" if b == "0" else "0" for b in EAN_L[int(ch)])
    return bits + "101"

def ean13_svg(code, mw=2, h=56):
    bits, qz = ean13_bits(code), 9
    W, H = (95 + 2 * qz) * mw, h + 16
    rects, i = "", 0
    while i < 95:
        if bits[i] == "1":
            j = i
            while j < 95 and bits[j] == "1":
                j += 1
            g = 6 if (i < 3 or 45 <= i < 50 or i >= 92) else 0
            rects += f'<rect x="{(qz + i) * mw}" y="0" width="{(j - i) * mw}" height="{h + g}"/>'
            i = j
        else:
            i += 1
    t = 'font-family="monospace" font-size="12" fill="#000"'
    txt = (f'<text x="{(qz - 4) * mw}" y="{H - 2}" text-anchor="middle" {t}>{code[0]}</text>'
           f'<text x="{(qz + 3) * mw}" y="{H - 2}" textLength="{42 * mw}" lengthAdjust="spacing" {t}>{code[1:7]}</text>'
           f'<text x="{(qz + 50) * mw}" y="{H - 2}" textLength="{42 * mw}" lengthAdjust="spacing" {t}>{code[7:]}</text>')
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">'
            f'<rect width="{W}" height="{H}" fill="#fff"/><g fill="#000">{rects}</g>{txt}</svg>')

def focus_script():
    lb = json.dumps(SCAN_LABEL)
    return ("<script>setTimeout(function(){try{var d=window.parent.document;var e=d.querySelector('input[aria-label=\"'+" + lb +
            "+'\"]');if(e){e.focus();}}catch(x){}},350);/*" + str(time.time()) + "*/</script>")

# ============================================================== العروض (أفضل عرض للعميل — بدون تجميع)
def active_offers(branch):
    today = datetime.date.today().isoformat()
    return qdf("SELECT * FROM offers WHERE active=1 AND (start_date='' OR start_date<=?) AND (end_date='' OR end_date>=?) "
               "AND (branch='الكل' OR branch=?)", (today, today, branch))

def offer_matches(o, it):
    s, v = o["scope"], str(o["scope_value"] or "")
    if s == "كل الأصناف":
        return True
    if s == "فئة":
        return it["category"] == v
    if s == "ماركة":
        return it["brand"] == v
    if s == "منشأ/جودة":
        return it["origin"] == v
    if s == "موديل":
        return it["model"] == v
    if s == "رقم OEM":
        return bool(v) and str(it["part_number"]).upper().startswith(v.upper())
    return False

def best_offer(it, qty, offers, lp):
    """أفضل عرض مطبّق (بدون تجميع عروض): يرجع (العرض أو None, قيمة الخصم للقطعة)."""
    best, bd = None, 0.0
    for _, o in offers.iterrows():
        if qty < int(o["min_qty"] or 1) or not offer_matches(o, it):
            continue
        d = lp * float(o["value"]) / 100 if o["type"] == OFFER_TYPES[0] else float(o["value"])
        d = min(max(d, 0.0), lp)
        if d > bd:
            best, bd = o, d
    return best, bd

def line_price(it, offers):
    lp = it["list"]
    if it["manual"] > 0:
        d, note = lp * it["manual"] / 100, f"خصم يدوي {it['manual']:g}%"
    else:
        o, d = best_offer(it, it["qty"], offers, lp)
        note = f"عرض: {o['name']}" if o is not None else ""
    it["price"], it["note"] = round(lp - d, 4), note

def cart_add(cart, r, qty, manual, offers):
    for it in cart:
        if it["id"] == int(r["id"]):
            it["qty"] += qty
            if manual > 0:
                it["manual"] = manual
            line_price(it, offers)
            return
    it = dict(id=int(r["id"]), pn=r["part_number"], part_number=r["part_number"], name=r["name"], model=r["model"],
              brand=r["brand"], origin=r["quality_origin"], category=r["category"], list=float(r["selling_price"]),
              cost=float(r["cost_price"] or 0), qty=int(qty), manual=float(manual))
    line_price(it, offers)
    cart.append(it)

# ============================================================== الفواتير والمرتجعات
INV_CSS = """<style>*{box-sizing:border-box}.inv{font-family:Tahoma,Arial,sans-serif;color:#111;background:#fff;padding:22px;
max-width:900px;margin:auto;border:1px solid #d5dbe3;border-radius:10px}.inv h2{margin:0;color:#0b1f33}.inv h4{margin:14px 0 6px;color:#b23}
.inv .sub{color:#555;font-size:13px;margin:2px 0}.inv .meta{display:flex;flex-wrap:wrap;gap:18px;background:#f3f6fa;
padding:10px 14px;border-radius:8px;margin:14px 0;font-size:14px}.inv table{width:100%;border-collapse:collapse;font-size:13px}
.inv td,.inv th{border:1px solid #c9d1db;padding:6px;text-align:center}.inv th{background:#0b1f33;color:#fff}
.inv .tot{margin-top:12px;text-align:left;font-size:15px}.inv .tot b{font-size:19px;color:#0b1f33}
.inv .foot{text-align:center;color:#666;font-size:12px;margin-top:16px}
.inv .btn{padding:9px 22px;font-size:15px;background:#1e88e5;color:#fff;border:0;border-radius:8px;cursor:pointer;margin-top:12px}
@media print{.np{display:none!important}.inv{border:0}@page{size:A4;margin:12mm}}</style>"""

def invoice_lines(no):
    return qdf("SELECT * FROM invoices WHERE invoice_no=? ORDER BY id", (no,))

def invoice_returns(no):
    return qdf("SELECT * FROM returns WHERE invoice_no=? ORDER BY id", (no,))

def invoice_html(no, df, rdf):
    """الفاتورة الأصلية تُعرض كما بيعت تماماً؛ المرتجعات في جدول منفصل أسفلها ✅ [تعديل 3]. كل النصوص عبر html.escape."""
    h = df.iloc[0]
    store, phone, addr = get_setting("store_name"), get_setting("store_phone"), get_setting("store_address")
    rows, before, disc = "", 0.0, 0.0
    for i, (_, r) in enumerate(df.iterrows(), 1):
        lp = r["list_price"] if r["list_price"] else r["unit_price"]
        before += r["qty"] * lp
        disc += r["qty"] * (lp - r["unit_price"])
        rows += (f"<tr><td>{i}</td><td>{html.escape(str(r['part_number']))}</td><td>{html.escape(str(r['name']))}</td>"
                 f"<td>{html.escape(str(r['model']))}</td><td>{html.escape(str(r['brand']))}</td>"
                 f"<td>{html.escape(str(r['quality_origin']))}</td><td>{r['qty']}</td><td>{lp:,.2f}</td>"
                 f"<td>{r['unit_price']:,.2f}</td><td>{r['qty'] * r['unit_price']:,.2f}</td></tr>")
    after = before - disc
    ret_total = float(rdf["amount"].sum()) if not rdf.empty else 0.0
    ret_html = ""
    if not rdf.empty:
        rr = "".join(f"<tr><td>{html.escape(str(x['date']))}</td><td>{html.escape(str(x['return_no']))}</td>"
                     f"<td>{html.escape(str(x['name']))} — {html.escape(str(x['brand']))}</td><td>{x['qty']}</td>"
                     f"<td>{x['amount']:,.2f}</td><td>{html.escape(str(x['reason'] or ''))}</td></tr>" for _, x in rdf.iterrows())
        ret_html = (f"<h4>المرتجعات على هذه الفاتورة</h4><table><tr><th>تاريخ المرتجع</th><th>رقم المرتجع</th><th>الصنف</th>"
                    f"<th>الكمية</th><th>المبلغ</th><th>السبب</th></tr>{rr}</table>")
    contact = " | ".join(x for x in [html.escape(phone), html.escape(addr)] if x)
    cust_phone = f" &nbsp;|&nbsp; <span><b>الهاتف:</b> {html.escape(str(h['customer_phone']))}</span>" if h["customer_phone"] else ""
    notes = sorted({str(n) for n in df["discount_note"].fillna("") if n})
    notes_txt = html.escape(" | ".join(notes))
    notes_html = f'<div class="sub" style="margin-top:8px"><b>العروض/الخصومات المطبقة:</b> {notes_txt}</div>' if notes else ""
    return (INV_CSS + f"""<div class="inv" dir="rtl"><div style="text-align:center"><h2>🚗 {html.escape(store)}</h2>
<div class="sub">{contact}</div><div class="sub"><b>فاتورة بيع</b></div></div>
<div class="meta"><span><b>رقم الفاتورة:</b> {html.escape(str(no))}</span><span><b>التاريخ:</b> {html.escape(str(h['date']))}</span>
<span><b>الفرع:</b> {html.escape(str(h['branch']))}</span><span><b>العميل:</b> {html.escape(str(h['customer']))}</span>{cust_phone}</div>
<table><tr><th>#</th><th>رقم OEM</th><th>الصنف</th><th>الموديل</th><th>الماركة</th><th>المنشأ</th><th>الكمية</th>
<th>السعر</th><th>بعد الخصم</th><th>الإجمالي</th></tr>{rows}</table>{notes_html}
<div class="tot">الإجمالي قبل الخصم: {before:,.2f} &nbsp;|&nbsp; الخصومات: {disc:,.2f} &nbsp;|&nbsp; إجمالي الفاتورة: <b>{after:,.2f} EGP</b></div>
{ret_html}{f'<div class="tot">المرتجعات: {ret_total:,.2f} &nbsp;|&nbsp; الصافي بعد المرتجعات: <b>{after - ret_total:,.2f} EGP</b></div>' if ret_total else ''}
<div class="foot">شكراً لتعاملكم معنا — يرجى الاحتفاظ بالفاتورة</div>
<div style="text-align:center"><button class="btn np" onclick="window.print()">🖨️ طباعة الفاتورة</button></div></div>""")

def invoice_text(no, df, rdf):
    h = df.iloc[0]
    lines = [f"{get_setting('store_name')}", f"فاتورة رقم: {no}", f"التاريخ: {h['date']}", f"العميل: {h['customer']}", "------"]
    total, disc = 0.0, 0.0
    for _, r in df.iterrows():
        lp = r["list_price"] if r["list_price"] else r["unit_price"]
        total += r["qty"] * r["unit_price"]
        disc += r["qty"] * (lp - r["unit_price"])
        lines.append(f"- {r['name']} | {r['model']} | {r['brand']} ({r['quality_origin']}) × {r['qty']} = {r['qty'] * r['unit_price']:,.2f}")
    if disc > 0.005:
        lines.append(f"إجمالي الخصم: {disc:,.2f}")
    lines += ["------", f"الإجمالي: {total:,.2f} EGP"]
    if not rdf.empty:
        ret = float(rdf["amount"].sum())
        lines += [f"مرتجعات: {ret:,.2f}", f"الصافي: {total - ret:,.2f} EGP"]
    lines.append("شكراً لتعاملكم معنا")
    return "\n".join(lines)

def wa_phone(p):
    d = "".join(ch for ch in str(p or "") if ch.isdigit())
    if d.startswith("00"):
        d = d[2:]
    if len(d) == 11 and d.startswith("0"):
        d = "20" + d[1:]
    return d

def show_invoice(no, key):
    df = invoice_lines(no)
    if df.empty:
        return
    rdf = invoice_returns(no)
    frag = invoice_html(no, df, rdf)
    components.html(frag, height=430 + 38 * (len(df) + len(rdf)), scrolling=True)
    full = (f'<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8"><title>{html.escape(str(no))}</title></head>'
            f"<body style='background:#f3f6fa;margin:0;padding:16px'>{frag}</body></html>")
    msg = invoice_text(no, df, rdf)
    wa = f"https://wa.me/{wa_phone(df.iloc[0]['customer_phone'])}?text={urllib.parse.quote(msg)}"
    mail = f"mailto:?subject={urllib.parse.quote('فاتورة ' + str(no))}&body={urllib.parse.quote(msg)}"
    a, b, c, d = st.columns(4)
    a.download_button("⬇️ تحميل الفاتورة (HTML)", full, file_name=f"{no}.html", mime="text/html", key=f"dh_{key}_{no}")
    b.download_button("📄 تحميل نص الفاتورة", msg, file_name=f"{no}.txt", mime="text/plain", key=f"dt_{key}_{no}")
    c.markdown(f'<a class="linkbtn" href="{html.escape(wa)}" target="_blank">💬 مشاركة عبر واتساب</a>', unsafe_allow_html=True)
    d.markdown(f'<a class="linkbtn mail" href="{html.escape(mail)}" target="_blank">✉️ مشاركة بالبريد</a>', unsafe_allow_html=True)
    st.caption("للطباعة اضغط زر الطباعة داخل الفاتورة، ولحفظها PDF اختر (Save as PDF) من نافذة الطباعة.")

def confirm_sale(branch, customer, phone, cart, dmode="بدون", dval=0.0):
    """✅ [تعديل 1+2] عملية البيع كلها في معاملة BEGIN IMMEDIATE واحدة:
       - الأسعار والتكلفة والعروض تُعاد قراءتها من قاعدة البيانات (لا نثق بأرقام الواجهة).
       - الحد الأقصى للخصم يُفحص على إجمالي الخصم الفعلي للفاتورة، ويُمنع إجمالي صفري.
       - رقم الفاتورة من عدّاد ذري، وخصم المخزون بـ UPDATE شرطي مع فحص rowcount.
       - أي خطأ ⇒ ROLLBACK كامل."""
    if not cart:
        raise ValueError("الفاتورة فارغة.")
    offers, maxd = active_offers(branch), max_discount()
    with tx() as c:
        need, cur = {}, {}
        for it in cart:
            need[it["id"]] = need.get(it["id"], 0) + int(it["qty"])
        for iid, n in need.items():
            r = c.execute("SELECT * FROM inventory WHERE id=? AND branch=?", (iid, branch)).fetchone()
            if r is None:
                raise ValueError("أحد الأصناف لم يعد موجوداً في هذا الفرع.")
            if r["quantity"] < n:
                raise ValueError(f"الكمية غير كافية للصنف: {r['name']} ({r['brand']}) - المتاح {r['quantity']}")
            cur[iid] = r
        items = []
        for it in cart:
            f = dict(it)
            f["list"], f["cost"] = float(cur[it["id"]]["selling_price"] or 0), float(cur[it["id"]]["cost_price"] or 0)
            line_price(f, offers)
            items.append(f)
        sub = sum(i["qty"] * i["price"] for i in items)
        before = sum(i["qty"] * i["list"] for i in items)
        dval = max(0.0, float(dval or 0))
        inv_disc = sub * dval / 100 if dmode == "نسبة %" else (dval if dmode == "مبلغ" else 0.0)
        inv_disc = min(inv_disc, sub)
        total = sub - inv_disc
        if total <= 0.005:
            raise ValueError("لا يمكن إصدار فاتورة بقيمة صفر.")
        eff = (before - total) / before * 100 if before > 0 else 0.0
        if eff > maxd + 1e-6:
            raise ValueError(f"إجمالي الخصم الفعلي {eff:.1f}% يتجاوز الحد المسموح ({maxd:g}%).")
        no = f"INV-{next_seq(c, 'invoice_seq'):06d}"
        now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
        for it in items:
            line_total = it["qty"] * it["price"]
            share = inv_disc * line_total / sub if sub > 0 else 0.0
            note = " + ".join(x for x in [it.get("note", ""), "خصم فاتورة" if inv_disc > 0 else ""] if x)
            u = c.execute("UPDATE inventory SET quantity=quantity-? WHERE id=? AND quantity>=?", (it["qty"], it["id"], it["qty"]))
            if u.rowcount != 1:
                raise ValueError(f"تغيّر رصيد الصنف {it['name']} أثناء البيع، أعد المحاولة.")
            c.execute("""INSERT INTO invoices(invoice_no,date,customer,customer_phone,branch,inventory_id,part_number,name,model,brand,
                quality_origin,qty,unit_price,total,unit_cost,list_price,discount_note) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                      (no, now, customer, phone, branch, it["id"], it["pn"], it["name"], it["model"], it["brand"], it["origin"],
                       it["qty"], (line_total - share) / it["qty"], line_total - share, it["cost"], it["list"], note))
    return no

def do_return(items, reason=""):
    """✅ [تعديل 1+3] المرتجع يُسجَّل في جدول returns فقط (الفاتورة لا تُمس)، ويعيد الكمية للمخزن داخل معاملة ذرية.
    المتبقي القابل للإرجاع يُحسب من جدول المرتجعات داخل المعاملة نفسها فلا يمكن إرجاع نفس الكمية مرتين."""
    with tx() as c:
        rn = f"RET-{next_seq(c, 'return_seq'):06d}"
        now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
        for lid, q in items:
            line = c.execute("SELECT * FROM invoices WHERE id=?", (lid,)).fetchone()
            if line is None:
                raise ValueError("بند الفاتورة غير موجود.")
            done = c.execute("SELECT COALESCE(SUM(qty),0) FROM returns WHERE invoice_line_id=?", (lid,)).fetchone()[0]
            if q <= 0 or q > line["qty"] - done:
                raise ValueError("كمية المرتجع أكبر من المتبقي القابل للإرجاع.")
            up = line["unit_price"] or 0
            c.execute("""INSERT INTO returns(return_no,date,invoice_no,invoice_line_id,inventory_id,branch,part_number,name,model,brand,
                quality_origin,qty,unit_price,unit_cost,list_price,amount,reason,customer) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                      (rn, now, line["invoice_no"], lid, line["inventory_id"], line["branch"], line["part_number"], line["name"],
                       line["model"], line["brand"], line["quality_origin"], int(q), up, line["unit_cost"] or 0,
                       line["list_price"] or up, int(q) * up, reason, line["customer"]))
            u = c.execute("UPDATE inventory SET quantity=quantity+? WHERE id=?", (int(q), line["inventory_id"]))
            if u.rowcount != 1:
                raise ValueError("الصنف المرتبط بهذه الفاتورة لم يعد موجوداً في المخزن.")
    return rn

# ============================================================== التصميم
CSS = """<style>
@import url('https://fonts.googleapis.com/css2?family=Cairo:wght@400;600;700;800&display=swap');
.stApp{background:#f3f6fa;color:#1b2733;direction:rtl;font-family:'Cairo',sans-serif}
input,textarea,button,select{font-family:'Cairo',sans-serif!important}
.block-container{padding-top:1.4rem;max-width:1400px}
#MainMenu,footer{visibility:hidden}header[data-testid="stHeader"]{background:transparent}
.stApp h1,.stApp h2,.stApp h3,.stApp h4{color:#0b1f33;font-weight:800}
.stApp label p,.stApp .stMarkdown p{color:#1b2733}
.stTextInput input,.stNumberInput input,.stTextArea textarea{background:#fff!important;color:#1b2733!important;border-radius:10px}
[data-baseweb="select"]>div{background:#fff!important;color:#1b2733!important;border-radius:10px}
[data-testid="stSidebar"]{background:linear-gradient(180deg,#0b1f33 0%,#12385c 100%);direction:rtl}
[data-testid="stSidebar"] label p,[data-testid="stSidebar"] p,[data-testid="stSidebar"] span,
[data-testid="stSidebar"] .stMarkdown p,[data-testid="stSidebar"] .stCaption{color:#e8eef5!important}
[data-testid="stSidebar"] [role="radiogroup"]>label{background:rgba(255,255,255,.06);border-radius:10px;padding:8px 12px;
margin-bottom:6px;width:100%;transition:.15s}
[data-testid="stSidebar"] [role="radiogroup"]>label:hover{background:rgba(255,255,255,.16)}
[data-testid="stSidebar"] [role="radiogroup"]>label:has(input:checked){background:#1e88e5}
.brand{text-align:center;color:#fff;font-size:1.25rem;font-weight:800;padding:8px 0 14px;line-height:1.7}
.brand small{display:block;color:#9fb6cc;font-weight:400;font-size:.8rem}
.page-head{background:linear-gradient(120deg,#0b1f33,#1e6aa8);border-radius:16px;padding:18px 26px;margin-bottom:18px;
box-shadow:0 4px 16px rgba(11,31,51,.18)}
.page-head h2,.page-head p{color:#fff!important;margin:0}.page-head p{opacity:.8;font-size:.9rem;margin-top:4px}
.kpi{background:#fff;border-radius:14px;padding:14px 16px;box-shadow:0 2px 10px rgba(15,42,67,.08);
border-top:4px solid var(--c);margin-bottom:12px;height:112px}
.kpi .kt{font-size:.85rem;color:#5b6b7c}.kpi .kv{font-size:1.55rem;font-weight:800;color:#0b1f33;margin:2px 0}
.kpi .ks{font-size:.75rem;color:#8795a5}
.blue{--c:#1e88e5}.green{--c:#2e9e6b}.red{--c:#d64545}.amber{--c:#e69b12}.teal{--c:#0aa3a3}.slate{--c:#5b6b7c}
.bcard{background:#fff;border-radius:14px;padding:14px 16px;box-shadow:0 2px 10px rgba(15,42,67,.08);
border-right:5px solid #1e88e5;margin-bottom:12px;font-size:.88rem;line-height:1.9}
.bcard h4{margin:0 0 4px;font-size:1.05rem}.bcard b{color:#0b1f33}.bad{color:#d64545;font-weight:700}
.stButton>button,.stDownloadButton>button,[data-testid="stFormSubmitButton"]>button{border-radius:10px;font-weight:700;
border:1px solid #1e88e5;color:#1e88e5;background:#fff}
.stButton>button:hover,.stDownloadButton>button:hover{background:#1e88e5;color:#fff;border-color:#1e88e5}
.stButton>button[kind="primary"],[data-testid="stBaseButton-primary"],[data-testid="stFormSubmitButton"]>button[kind="primaryFormSubmit"]{
background:#1e88e5;color:#fff;border:0}
[data-testid="stSidebar"] .stButton>button{background:rgba(255,255,255,.1);color:#fff;border:1px solid rgba(255,255,255,.3);width:100%}
[data-testid="stDataFrame"],[data-testid="stDataEditor"]{direction:ltr;border-radius:12px;overflow:hidden}
.linkbtn{display:inline-block;padding:.5rem 1rem;border-radius:10px;background:#25d366;color:#fff!important;font-weight:700;
text-decoration:none;font-size:.9rem}.linkbtn.mail{background:#5b6b7c}
.login-card{background:#fff;border-radius:18px;padding:28px;box-shadow:0 8px 30px rgba(11,31,51,.15);text-align:center;margin-top:8vh}
.login-card h2{margin:6px 0}
</style>"""

def head(icon, title, sub=""):
    st.markdown(f'<div class="page-head"><h2>{icon} {html.escape(title)}</h2><p>{html.escape(sub)}</p></div>', unsafe_allow_html=True)

def kpi(title, value, sub="", tone="blue"):
    return f'<div class="kpi {tone}"><div class="kt">{title}</div><div class="kv">{value}</div><div class="ks">{sub}</div></div>'

def egp(x):
    return f"{x:,.0f} ج.م"

def csv_btn(df, label, name, key):
    st.download_button(label, df.to_csv(index=False).encode("utf-8-sig"), name, "text/csv", key=key)

# ============================================================== الصفحات
def first_run_screen():
    """✅ [تعديل 4] شاشة أول تشغيل: البيانات التجريبية اختيارية."""
    head("🚀", "مرحباً بك في النظام", "اختر طريقة البدء")
    st.write("يمكنك تجربة النظام ببيانات جاهزة (300 صنف مرسيدس موزعة على 4 فروع)، أو البدء بقاعدة فارغة لإدخال بياناتك الحقيقية. "
             "البيانات التجريبية يمكن حذفها لاحقاً بضغطة واحدة من صفحة الإعدادات.")
    a, b = st.columns(2)
    if a.button("📦 تحميل بيانات تجريبية (300 صنف)", type="primary"):
        n = load_demo()
        st.session_state["flash"] = f"تم تحميل {n} صنف تجريبي."
        st.rerun()
    if b.button("🆕 البدء بقاعدة فارغة"):
        set_setting("setup_done", "1")
        st.rerun()

def page_dashboard():
    head("📈", "لوحة التحكم الرئيسية", "نظرة شاملة ومحدثة على كل الفروع")
    if st.session_state.get("flash"):
        st.success(st.session_state.pop("flash"))
    if get_setting("pw_default", "0") == "1":
        st.warning("⚠️ كلمة المرور الحالية هي الافتراضية. غيّرها الآن من صفحة الإعدادات لحماية بياناتك.")
    period = st.radio("الفترة الزمنية", PERIODS, horizontal=True, key="d_period")
    inv, sal, daily, top, lows = dashboard_data(period)
    t, s = inv.sum(), sal.sum()
    r1 = st.columns(4)
    r1[0].markdown(kpi("إجمالي المبيعات", egp(s["gross"]), f"{int(s['n'])} فاتورة", "blue"), unsafe_allow_html=True)
    r1[1].markdown(kpi("المرتجعات", egp(s["ret"]), "بتاريخ تسجيل المرتجع", "red"), unsafe_allow_html=True)
    r1[2].markdown(kpi("صافي المبيعات", egp(s["net"]), "بعد خصم المرتجعات", "teal"), unsafe_allow_html=True)
    r1[3].markdown(kpi("صافي الأرباح", egp(s["profit"]), "المبيعات − التكلفة − أثر المرتجعات", "green"), unsafe_allow_html=True)
    r2 = st.columns(4)
    r2[0].markdown(kpi("قيمة المخزون (بسعر البيع)", egp(t["val_sell"]), f"{int(t['pieces']):,} قطعة", "blue"), unsafe_allow_html=True)
    r2[1].markdown(kpi("قيمة المخزون (بالتكلفة)", egp(t["val_cost"]), f"ربح متوقع {egp(t['val_sell'] - t['val_cost'])}", "slate"), unsafe_allow_html=True)
    r2[2].markdown(kpi("أصناف المخزون", f"{int(t['items']):,}", "في كل الفروع", "teal"), unsafe_allow_html=True)
    r2[3].markdown(kpi("تنبيهات النواقص", f"{int(t['low'])}", f"منها {int(t['zero'])} نفدت تماماً (الحد {low_limit()})", "amber"), unsafe_allow_html=True)
    today = datetime.date.today().isoformat()
    n_off = int(qdf("SELECT COUNT(*) c FROM offers WHERE active=1 AND (start_date='' OR start_date<=?) AND (end_date='' OR end_date>=?)",
                    (today, today)).iloc[0, 0])
    r3 = st.columns(4)
    r3[0].markdown(kpi("الخصومات الممنوحة", egp(s["disc"]), "عروض + خصومات يدوية + خصم الفواتير", "amber"), unsafe_allow_html=True)
    r3[1].markdown(kpi("المبيعات قبل الخصم", egp(s["gross"] + s["disc"]), "بأسعار القائمة", "slate"), unsafe_allow_html=True)
    r3[2].markdown(kpi("العروض الفعّالة", f"{n_off}", "تُطبَّق تلقائياً في POS", "teal"), unsafe_allow_html=True)
    r3[3].markdown(kpi("متوسط الفاتورة", egp(s["gross"] / s["n"] if s["n"] else 0), "قبل المرتجعات", "blue"), unsafe_allow_html=True)
    st.subheader("أداء الفروع")
    for col, b in zip(st.columns(4), BRANCHES):
        col.markdown(f"""<div class="bcard"><h4>🏬 {b}</h4>
صافي المبيعات: <b>{egp(sal.loc[b, 'net'])}</b><br>صافي الربح: <b>{egp(sal.loc[b, 'profit'])}</b><br>
المرتجعات: <b>{egp(sal.loc[b, 'ret'])}</b><br>قيمة المخزون: <b>{egp(inv.loc[b, 'val_sell'])}</b><br>
نواقص: <span class="bad">{int(inv.loc[b, 'low'])}</span> صنف</div>""", unsafe_allow_html=True)
    c1, c2 = st.columns(2)
    c1.subheader("المبيعات والأرباح حسب الفرع")
    c1.bar_chart(pd.DataFrame({"صافي المبيعات": sal["net"], "صافي الربح": sal["profit"]}))
    c2.subheader("صافي المبيعات اليومي")
    if daily.empty:
        c2.info("لا توجد حركة في هذه الفترة.")
    else:
        c2.line_chart(daily.set_index("d")["s"])
    c3, c4 = st.columns(2)
    c3.subheader("🏆 الأكثر مبيعاً (صافي)")
    if top.empty:
        c3.info("لا توجد مبيعات بعد.")
    else:
        c3.dataframe(top.rename(columns={"name": "الصنف", "model": "الموديل", "pieces": "القطع", "net": "صافي المبيعات"}), hide_index=True)
    c4.subheader("⚠️ أهم النواقص")
    if lows.empty:
        c4.success("لا توجد نواقص 👌")
    else:
        c4.dataframe(show(lows)[["الفرع", "اسم القطعة", "الموديل", "الماركة", "الكمية", "مكان التخزين"]], hide_index=True)

def page_search():
    head("🔍", "البحث الذكي الموحد", "يتجاهل الهمزات والتاء المربوطة والمسافات الزائدة — ابحث بأي جزء من البيانات")
    q = st.text_input("كلمات البحث", key="s_q", placeholder="مثال: تيل W205 bosch  |  A2054200  |  تايواني  |  A-07")
    br = st.selectbox("الفرع", ["الكل"] + BRANCHES, key="s_br")
    df = search_inv(q, br)
    st.caption(f"عدد النتائج: {len(df)}")
    st.dataframe(show(df).drop(columns=["م"]), hide_index=True)

def page_pos():
    head("🧾", "شاشة المبيعات (POS)", "ابحث أو امسح الباركود، واختر الماركة، وتُطبَّق العروض والخصومات تلقائياً")
    # ✅ [تعديل 2] كل حقول الفاتورة بمفاتيح مرتبطة برقم نسخة (v). تغيير v = تصفير كامل لكل الحقول.
    #    lv ينتقل بعد كل إضافة صنف فيُصفَّر عدد القطع والخصم اليدوي (فلا يتكرر الخصم على الصنف التالي).
    v, lv = st.session_state.setdefault("pos_v", 0), st.session_state.setdefault("pos_lv", 0)
    for k in list(st.session_state.keys()):                      # تنظيف مفاتيح النسخ القديمة قبل إنشاء الأدوات
        m = re.match(r"^pos_[a-z]+_(\d+)(?:_(\d+))?$", k)
        if m and (int(m.group(1)) != v or (m.group(2) is not None and int(m.group(2)) != lv)):
            del st.session_state[k]
    c1, c2, c3 = st.columns(3)
    branch = c1.selectbox("الفرع", BRANCHES, key="pos_branch")
    customer = c2.text_input("اسم العميل", key=f"pos_cust_{v}")
    phone = c3.text_input("رقم هاتف العميل (لمشاركة الفاتورة واتساب)", key=f"pos_phone_{v}")
    cart = st.session_state.setdefault("cart", [])
    if cart and st.session_state.get("cart_branch") != branch:
        cart.clear()
    offers, maxd = active_offers(branch), max_discount()
    if not offers.empty:
        st.info("🏷️ عروض فعّالة في هذا الفرع: " + " ، ".join(offers["name"].tolist()))
    # --- المسح بالباركود (قارئ الباركود يكتب الرقم ثم Enter)
    with st.form("scan_form", clear_on_submit=True):
        code = st.text_input(SCAN_LABEL, key=f"pos_scan_{v}")
        scanned = st.form_submit_button("➕ إضافة بالباركود")
    components.html(focus_script(), height=0)
    if scanned and code.strip():
        code = code.strip()
        m = qdf("SELECT * FROM inventory WHERE branch=? AND barcode=?", (branch, code))
        if m.empty:   # ✅ [تعديل 5] رقم OEM الآن قد يطابق عدة ماركات
            m = qdf("SELECT * FROM inventory WHERE branch=? AND part_number=? COLLATE NOCASE", (branch, code))
        if m.empty:
            o2 = qdf("SELECT branch,quantity FROM inventory WHERE barcode=? OR part_number=? COLLATE NOCASE", (code, code))
            if o2.empty:
                st.error(f"الباركود {code} غير مسجل في النظام.")
            else:
                st.warning("الصنف غير موجود في هذا الفرع، متوفر في: " + " ، ".join(f"{r['branch']} ({r['quantity']})" for _, r in o2.iterrows()))
        elif len(m) > 1:
            st.warning("هذا الرقم يخص عدة ماركات: " + " ، ".join(m["brand"].tolist()) + " — استخدم البحث بالأسفل لاختيار الماركة.")
        else:
            r = m.iloc[0]
            in_cart = sum(i["qty"] for i in cart if i["id"] == int(r["id"]))
            if r["quantity"] <= in_cart:
                st.error(f"نفدت الكمية المتاحة من {r['name']} ({r['brand']}).")
            else:
                cart_add(cart, r, 1, 0.0, offers)
                st.session_state["cart_branch"] = branch
                st.success(f"✔️ تمت إضافة: {r['name']} — {r['brand']} ({r['quality_origin']})")
    # --- البحث اليدوي
    text = st.text_input("🔍 ابحث عن القطعة (OEM / اسم / موديل / ماركة / منشأ / باركود)", key=f"pos_q_{v}")
    if text.strip():
        res = search_inv(text, branch)
        if res.empty:
            st.warning("لا توجد نتائج في هذا الفرع.")
        else:
            groups = res.groupby(["name", "model"], sort=False).size().reset_index()
            gmap = {f"{r['name']} | {r['model']}": (r["name"], r["model"]) for _, r in groups.iterrows()}
            nm, md = gmap[st.selectbox("اختر القطعة", list(gmap.keys()), key=f"pos_sel_{v}")]
            alts = qdf(f"SELECT {INV_COLS} FROM inventory WHERE branch=? AND name=? AND model=? ORDER BY selling_price DESC", (branch, nm, md))
            q1, q2 = st.columns(2)
            qty = q1.number_input("الكمية", min_value=1, value=1, step=1, key=f"pos_qty_{v}_{lv}")
            manual = q2.number_input(f"خصم يدوي على الصنف % (أقصى {maxd:g}%) — يحل محل العرض", min_value=0.0,
                                     max_value=float(maxd) if maxd > 0 else 1.0, value=0.0, step=1.0,
                                     key=f"pos_manual_{v}_{lv}", disabled=maxd <= 0)
            st.subheader("البدائل والماركات المتاحة لنفس القطعة والموديل")
            rows = []
            for _, a in alts.iterrows():
                lp = float(a["selling_price"])
                o, d = best_offer(dict(part_number=a["part_number"], category=a["category"], brand=a["brand"],
                                       origin=a["quality_origin"], model=a["model"]), int(qty), offers, lp)
                rows.append({"رقم OEM": a["part_number"], "الماركة": a["brand"], "المنشأ/الجودة": a["quality_origin"],
                             "الباركود": a["barcode"], "سعر البيع": lp, "العرض": o["name"] if o is not None else "—",
                             "السعر بعد العرض": lp - d, "الكمية": a["quantity"], "مكان التخزين": a["location"]})
            st.dataframe(pd.DataFrame(rows), hide_index=True)
            opts = {f"{r['brand']} - {r['quality_origin']} | {r['selling_price']:,.0f} ج.م | متاح {r['quantity']}": r
                    for _, r in alts.iterrows()}
            r = opts[st.selectbox("اختر الماركة/المنشأ", list(opts.keys()), key=f"pos_alt_{v}")]
            if st.button("➕ إضافة للفاتورة", type="primary"):
                in_cart = sum(i["qty"] for i in cart if i["id"] == int(r["id"]))
                if qty + in_cart > r["quantity"]:
                    st.error(f"الكمية المطلوبة أكبر من المتاح ({r['quantity']}).")
                else:
                    cart_add(cart, r, int(qty), float(manual), offers)
                    st.session_state["cart_branch"] = branch
                    st.session_state["pos_lv"] = lv + 1       # تصفير الكمية والخصم اليدوي للصنف التالي
                    st.rerun()
            other = qdf("SELECT branch,brand,quality_origin,quantity,selling_price,location FROM inventory "
                        "WHERE name=? AND model=? AND branch<>? ORDER BY branch", (nm, md, branch))
            if not other.empty:
                with st.expander("توفر نفس القطعة في الفروع الأخرى"):
                    st.dataframe(show(other), hide_index=True)
    # --- الفاتورة
    st.subheader("🛒 بنود الفاتورة")
    if cart:
        for it in cart:
            line_price(it, offers)
        for i, it in enumerate(cart):
            a, b = st.columns([8, 1])
            note_txt = f" ({it['note']})" if it["note"] else ""
            a.write(f"{i + 1}. {it['name']} | {it['model']} | {it['brand']} ({it['origin']}) × {it['qty']} | "
                    f"{it['list']:,.2f} ← {it['price']:,.2f}{note_txt} = {it['qty'] * it['price']:,.2f} EGP")
            if b.button("🗑️", key=f"pos_rm_{v}_{i}"):
                cart.pop(i); st.rerun()
        sub = sum(i["qty"] * i["price"] for i in cart)
        before = sum(i["qty"] * i["list"] for i in cart)
        d1, d2 = st.columns(2)
        dmode = d1.radio("خصم إضافي على إجمالي الفاتورة", ["بدون", "نسبة %", "مبلغ"], horizontal=True, key=f"pos_dmode_{v}")
        dval = d2.number_input("قيمة الخصم", min_value=0.0, value=0.0, step=1.0, key=f"pos_dval_{v}", disabled=(dmode == "بدون"))
        dval = 0.0 if dmode == "بدون" else float(dval)
        inv_disc = min(sub * dval / 100 if dmode == "نسبة %" else dval, sub)
        total = sub - inv_disc
        # ✅ [تعديل 2] الحد الأقصى على إجمالي الخصم الفعلي (عروض + يدوي + خصم الفاتورة) وليس على النسبة اليدوية فقط
        eff = (before - total) / before * 100 if before > 0 else 0.0
        over, zero = eff > maxd + 1e-6, total <= 0.005
        if over:
            st.error(f"إجمالي الخصم الفعلي {eff:.1f}% يتجاوز الحد المسموح ({maxd:g}%). قلّل الخصم أو غيّر الحد من الإعدادات.")
        if zero:
            st.error("لا يمكن إصدار فاتورة بقيمة صفر.")
        if total < sum(i["qty"] * i["cost"] for i in cart):
            st.warning("⚠️ تنبيه: الفاتورة بعد الخصم أقل من إجمالي التكلفة.")
        k = st.columns(4)
        k[0].markdown(kpi("قبل الخصم", egp(before), "بأسعار القائمة", "slate"), unsafe_allow_html=True)
        k[1].markdown(kpi("خصم الأصناف/العروض", egp(before - sub), "", "amber"), unsafe_allow_html=True)
        k[2].markdown(kpi("خصم الفاتورة", egp(inv_disc), "", "amber"), unsafe_allow_html=True)
        k[3].markdown(kpi("الإجمالي النهائي", egp(total), f"إجمالي الخصم الفعلي {eff:.1f}% (الحد {maxd:g}%)",
                          "red" if over else "green"), unsafe_allow_html=True)
        if st.button("✅ تأكيد البيع وإصدار الفاتورة", type="primary", key=f"pos_confirm_{v}", disabled=over or zero):
            try:
                no = confirm_sale(branch, customer.strip() or "عميل نقدي", phone.strip(), cart, dmode, dval)
            except ValueError as e:
                st.error(str(e))
            except sqlite3.Error:
                st.error("تعذر إتمام العملية الآن (قاعدة البيانات مشغولة أو حدث تعارض). لم يُحفظ شيء — أعد المحاولة.")
            else:
                st.session_state["last_invoice"] = no
                cart.clear()
                st.session_state.pop("cart_branch", None)
                st.session_state["pos_v"], st.session_state["pos_lv"] = v + 1, 0   # ✅ [تعديل 2] تصفير كامل
                st.rerun()
    else:
        st.info("الفاتورة فارغة.")
    no = st.session_state.get("last_invoice")
    if no:
        st.success(f"تم إصدار الفاتورة {no} وخصم الكميات من المخزن.")
        show_invoice(no, "pos")
        if st.button("🆕 فاتورة جديدة"):
            st.session_state.pop("last_invoice", None)
            st.session_state.pop("cart_branch", None)
            cart.clear()
            st.session_state["pos_v"], st.session_state["pos_lv"] = v + 1, 0       # ✅ [تعديل 2] تصفير كامل
            st.rerun()

def page_inventory():
    head("📦", "إدارة وتعديل المخزون", "تعديل الكميات والأسعار وأماكن التخزين وإضافة أصناف جديدة")
    brands = qdf("SELECT DISTINCT brand FROM inventory ORDER BY brand")["brand"].tolist()
    c1, c2, c3 = st.columns(3)
    br = c1.selectbox("الفرع", ["الكل"] + BRANCHES, key="inv_br")
    bd = c2.selectbox("الماركة", ["الكل"] + brands, key="inv_bd")
    og = c3.selectbox("المنشأ/الجودة", ["الكل"] + ORIGINS, key="inv_og")
    q = st.text_input("🔍 بحث شامل موحد", key="inv_q")
    orig = show(search_inv(q, br, bd, og)).reset_index(drop=True)
    orig[AR["location"]] = orig[AR["location"]].fillna("")
    st.caption(f"عدد الأصناف: {len(orig)} — عدّل (الكمية / التكلفة / سعر البيع / مكان التخزين) ثم اضغط حفظ.")
    num_cols = [AR["quantity"], AR["cost_price"], AR["selling_price"]]
    ver = st.session_state.get("inv_v", 0)
    ed = st.data_editor(orig, hide_index=True, key=f"ed_{br}_{bd}_{og}_{q}_{ver}",
                        disabled=[c for c in orig.columns if c not in num_cols + [AR["location"]]],
                        column_config={AR["quantity"]: st.column_config.NumberColumn(min_value=0, step=1),
                                       AR["cost_price"]: st.column_config.NumberColumn(min_value=0),
                                       AR["selling_price"]: st.column_config.NumberColumn(min_value=0)})
    a, b = st.columns([1, 4])
    if a.button("💾 حفظ التعديلات", type="primary"):
        changes = []
        for i in ed.index:
            o, e = orig.loc[i], ed.loc[i]
            if any(float(o[c]) != float(e[c]) for c in num_cols) or str(o[AR["location"]]) != str(e[AR["location"]] or ""):
                if any(pd.isna(e[c]) or float(e[c]) < 0 for c in num_cols):
                    st.error(f"قيم غير صحيحة للصنف {e[AR['part_number']]}"); changes = None; break
                changes.append((int(e[AR["quantity"]]), float(e[AR["cost_price"]]), float(e[AR["selling_price"]]),
                                str(e[AR["location"]] or "").strip(), int(o[AR["id"]])))
        if changes:
            with tx() as c:   # كل التعديلات معاً أو لا شيء
                c.executemany("UPDATE inventory SET quantity=?, cost_price=?, selling_price=?, location=? WHERE id=?", changes)
            st.session_state["inv_v"] = ver + 1
            st.success(f"تم تحديث {len(changes)} صنف."); st.rerun()
        elif changes is not None:
            st.info("لا توجد تعديلات.")
    with b:
        csv_btn(orig, "⬇️ تصدير الجدول (CSV)", "inventory.csv", "inv_csv")
    st.divider()
    st.subheader("➕ إضافة قطعة جديدة")
    st.caption("يمكن تكرار نفس رقم OEM بماركة/منشأ مختلف أو في فرع آخر. الممنوع فقط تكرار (الرقم + الماركة + المنشأ + الفرع).")
    with st.form("add_part", clear_on_submit=True):
        a, b, c = st.columns(3)
        pn, name, cat = a.text_input("رقم OEM"), b.text_input("اسم القطعة"), c.text_input("الفئة")
        model, brand, origin = a.text_input("الموديل"), b.text_input("الماركة"), c.selectbox("المنشأ/الجودة", ORIGINS)
        origin2, branch, loc = a.text_input("منشأ آخر (اختياري)"), b.selectbox("الفرع", BRANCHES), c.text_input("مكان التخزين (رف/صف)")
        qty = a.number_input("الكمية", min_value=0, value=0, step=1)
        cp = b.number_input("سعر التكلفة", min_value=0.0, value=0.0, step=10.0)
        sp = c.number_input("سعر البيع", min_value=0.0, value=0.0, step=10.0)
        barcode = a.text_input("الباركود (اتركه فارغاً للتوليد/إعادة الاستخدام التلقائي)")
        if st.form_submit_button("حفظ القطعة", type="primary"):
            pn, brand, bc_in, org = pn.strip(), brand.strip(), barcode.strip(), (origin2.strip() or origin)
            if not pn or not name.strip() or not brand:
                st.error("رقم OEM والاسم والماركة مطلوبة.")
            elif not qdf("SELECT id FROM inventory WHERE part_number=? COLLATE NOCASE AND brand=? COLLATE NOCASE "
                         "AND quality_origin=? AND branch=?", (pn, brand, org, branch)).empty:
                st.error("هذا الصنف (نفس الرقم والماركة والمنشأ) موجود بالفعل في هذا الفرع!")
            elif bc_in and not qdf(f"SELECT id FROM inventory WHERE barcode=? AND NOT ({VARIANT_SQL})", (bc_in, pn, brand, org)).empty:
                st.error("هذا الباركود مستخدم لمنتج آخر!")
            else:
                try:
                    with tx() as c:
                        if not bc_in:   # نفس المنتج في فرع آخر ⇒ نفس الباركود
                            same = c.execute(f"SELECT barcode FROM inventory WHERE {VARIANT_SQL} AND barcode<>'' LIMIT 1", (pn, brand, org)).fetchone()
                            bc_in = same["barcode"] if same else ""
                        cur = c.execute("""INSERT INTO inventory(part_number,name,category,model,brand,quality_origin,quantity,cost_price,
                            selling_price,branch,location,barcode) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
                                        (pn, name.strip(), cat.strip(), model.strip(), brand, org, int(qty), cp, sp, branch, loc.strip(), bc_in))
                        if not bc_in:
                            c.execute("UPDATE inventory SET barcode=? WHERE id=?", (internal_barcode(cur.lastrowid), cur.lastrowid))
                    st.success("تمت إضافة القطعة."); st.rerun()
                except sqlite3.IntegrityError:
                    st.error("تعذر الحفظ: الصنف موجود بالفعل.")

def page_transfer():
    head("🔄", "تحويل المخزون بين الفروع", "نقل كمية من صنف محدد بماركته من فرع إلى آخر")
    c1, c2 = st.columns(2)
    src = c1.selectbox("من فرع", BRANCHES, key="tr_src")
    dst = c2.selectbox("إلى فرع", [b for b in BRANCHES if b != src], key="tr_dst")
    q = st.text_input("🔍 ابحث عن الصنف", key="tr_q")
    df = search_inv(q, src)
    df = df[df["quantity"] > 0]
    if df.empty:
        st.info("لا توجد أصناف متاحة للتحويل بهذا البحث.")
    else:
        opts = {f"{r['part_number']} | {r['name']} | {r['model']} | {r['brand']} ({r['quality_origin']}) | متاح {r['quantity']}": r
                for _, r in df.iterrows()}
        r = opts[st.selectbox("الصنف", list(opts.keys()), key="tr_item")]
        a, b = st.columns(2)
        qty = a.number_input("الكمية المنقولة", min_value=1, max_value=int(r["quantity"]), value=1, step=1, key="tr_qty")
        newloc = b.text_input("مكان التخزين في الفرع المستلم (إذا كان الصنف جديداً عليه)", key="tr_loc")
        if st.button("نقل الكمية", type="primary"):
            try:
                with tx() as c:   # ✅ [تعديل 1] خصم من المصدر بشرط الرصيد + إضافة للوجهة + سجل — معاملة واحدة
                    u = c.execute("UPDATE inventory SET quantity=quantity-? WHERE id=? AND quantity>=?", (int(qty), int(r["id"]), int(qty)))
                    if u.rowcount != 1:
                        raise ValueError("الرصيد غير كافٍ في الفرع المصدر.")
                    d = c.execute("SELECT id FROM inventory WHERE part_number=? COLLATE NOCASE AND brand=? COLLATE NOCASE "
                                  "AND quality_origin=? AND branch=?", (r["part_number"], r["brand"], r["quality_origin"], dst)).fetchone()
                    if d:
                        c.execute("UPDATE inventory SET quantity=quantity+? WHERE id=?", (int(qty), d["id"]))
                    else:   # ✅ [تعديل 5] نفس رقم OEM في الفرع الجديد بدون أي لاحقة
                        c.execute("""INSERT INTO inventory(part_number,name,category,model,brand,quality_origin,quantity,cost_price,
                            selling_price,branch,location,barcode) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
                                  (r["part_number"], r["name"], r["category"], r["model"], r["brand"], r["quality_origin"], int(qty),
                                   r["cost_price"], r["selling_price"], dst, newloc.strip() or "غير محدد", r["barcode"]))
                    c.execute("INSERT INTO transfers(date,part_number,name,brand,quality_origin,from_branch,to_branch,qty) VALUES (?,?,?,?,?,?,?,?)",
                              (datetime.datetime.now().strftime("%Y-%m-%d %H:%M"), r["part_number"], r["name"], r["brand"],
                               r["quality_origin"], src, dst, int(qty)))
                st.success(f"تم نقل {qty} قطعة من {src} إلى {dst} وتحديث الرصيدين.")
            except ValueError as e:
                st.error(str(e))
            except sqlite3.Error:
                st.error("فشل التحويل ولم يتغير أي رصيد. أعد المحاولة.")
    st.subheader("سجل آخر التحويلات")
    log = qdf("SELECT date,part_number,name,brand,quality_origin,from_branch,to_branch,qty FROM transfers ORDER BY id DESC LIMIT 30")
    st.dataframe(log.rename(columns={"date": "التاريخ", "part_number": "رقم OEM", "name": "الصنف", "brand": "الماركة",
                                     "quality_origin": "المنشأ", "from_branch": "من", "to_branch": "إلى", "qty": "الكمية"}), hide_index=True)

def page_returns():
    head("↩️", "مرتجعات المبيعات", "تُسجَّل في جدول مستقل ولا تُعدِّل الفاتورة الأصلية؛ وتعيد الكمية للمخزن تلقائياً")
    if st.session_state.get("ret_flash"):
        st.success(st.session_state.pop("ret_flash"))
    raw = st.text_input("رقم الفاتورة (مثال: INV-000001 أو 1)", key="ret_no").strip().upper()
    if raw:
        no = f"INV-{int(raw):06d}" if raw.isdigit() else raw
        df = qdf("""SELECT i.*, COALESCE((SELECT SUM(r.qty) FROM returns r WHERE r.invoice_line_id=i.id),0) AS returned
                    FROM invoices i WHERE i.invoice_no=? ORDER BY i.id""", (no,))
        if df.empty:
            st.error("الفاتورة غير موجودة.")
        else:
            st.write(f"العميل: **{df.iloc[0]['customer']}** | الفرع: **{df.iloc[0]['branch']}** | التاريخ: {df.iloc[0]['date']}")
            st.dataframe(df[["part_number", "name", "model", "brand", "quality_origin", "qty", "returned", "unit_price"]].rename(
                columns={**AR, "qty": "الكمية المباعة", "returned": "المرتجع سابقاً", "unit_price": "سعر الوحدة (بعد الخصم)"}), hide_index=True)
            df["rem"] = df["qty"] - df["returned"]
            avail = df[df["rem"] > 0]
            if avail.empty:
                st.info("تم إرجاع هذه الفاتورة بالكامل.")
            else:
                r1, r2 = st.columns(2)
                reason = r1.selectbox("سبب المرتجع", RETURN_REASONS, key="ret_reason")
                note = r2.text_input("ملاحظات (اختياري)", key="ret_note").strip()
                full_reason = reason + (f" — {note}" if note else "")
                mode = st.radio("نوع المرتجع", ["إرجاع الفاتورة بالكامل", "إرجاع صنف/كمية محددة"], key="ret_mode", horizontal=True)
                items = None
                if mode.startswith("إرجاع الفاتورة"):
                    if st.button("تنفيذ إرجاع كامل الفاتورة", type="primary"):
                        items = [(int(r["id"]), int(r["rem"])) for _, r in avail.iterrows()]
                else:
                    opts = {f"{r['name']} | {r['brand']} ({r['quality_origin']}) | المتبقي للإرجاع {r['rem']}": r for _, r in avail.iterrows()}
                    r = opts[st.selectbox("الصنف", list(opts.keys()), key="ret_item")]
                    q = st.number_input("كمية المرتجع", min_value=1, max_value=int(r["rem"]), value=1, step=1, key="ret_qty")
                    if st.button("تنفيذ المرتجع", type="primary"):
                        items = [(int(r["id"]), int(q))]
                if items:
                    try:
                        rn = do_return(items, full_reason)
                        st.session_state["ret_flash"] = f"تم تسجيل المرتجع {rn} وإعادة الكميات للمخزن."
                        st.rerun()
                    except ValueError as e:
                        st.error(str(e))
                    except sqlite3.Error:
                        st.error("تعذر تسجيل المرتجع ولم يتغير شيء. أعد المحاولة.")
    st.divider()
    st.subheader("📜 سجل المرتجعات")
    log = qdf("SELECT return_no,date,invoice_no,branch,name,brand,qty,amount,reason FROM returns ORDER BY id DESC LIMIT 100")
    out = log.rename(columns={"return_no": "رقم المرتجع", "date": "تاريخ المرتجع", "invoice_no": "الفاتورة", "branch": "الفرع",
                              "name": "الصنف", "brand": "الماركة", "qty": "الكمية", "amount": "المبلغ", "reason": "السبب"})
    st.dataframe(out, hide_index=True)
    if not out.empty:
        csv_btn(out, "⬇️ تصدير المرتجعات (CSV)", "returns.csv", "ret_csv")

def page_history():
    head("🗂️", "سجل الفواتير والمبيعات", "بحث وعرض وطباعة ومشاركة الفواتير السابقة")
    c1, c2 = st.columns(2)
    q = c1.text_input("بحث برقم الفاتورة أو اسم العميل أو هاتفه", key="h_q")
    br = c2.selectbox("الفرع", ["الكل"] + BRANCHES, key="h_br")
    sql = """SELECT i.invoice_no, MIN(i.date) date, i.customer, i.customer_phone, i.branch, SUM(i.qty) qty,
        COALESCE((SELECT SUM(r.qty) FROM returns r WHERE r.invoice_no=i.invoice_no),0) returned,
        SUM(i.qty*(COALESCE(NULLIF(i.list_price,0),i.unit_price)-i.unit_price)) discount,
        SUM(i.qty*i.unit_price) total,
        SUM(i.qty*i.unit_price) - COALESCE((SELECT SUM(r.amount) FROM returns r WHERE r.invoice_no=i.invoice_no),0) net_total
        FROM invoices i WHERE 1=1"""
    p = []
    for tok in norm_text(q).split():   # ✅ [تعديل 6] بحث مطبَّع في الفواتير أيضاً
        sql += " AND (INSTR(norm(i.invoice_no),?)>0 OR INSTR(norm(i.customer),?)>0 OR INSTR(norm(i.customer_phone),?)>0)"
        p += [tok] * 3
    if br != "الكل":
        sql += " AND i.branch=?"; p.append(br)
    df = qdf(sql + " GROUP BY i.invoice_no ORDER BY i.invoice_no DESC", p)
    df["status"] = df.apply(lambda r: "مرتجعة" if r["returned"] >= r["qty"] else ("مرتجعة جزئياً" if r["returned"] > 0 else "مكتملة"), axis=1) \
        if not df.empty else []
    ren = {"invoice_no": "رقم الفاتورة", "date": "التاريخ", "customer": "العميل", "customer_phone": "الهاتف", "branch": "الفرع",
           "qty": "عدد القطع", "returned": "المرتجع", "discount": "الخصم", "total": "إجمالي الفاتورة",
           "net_total": "الصافي بعد المرتجعات", "status": "الحالة"}
    st.dataframe(df.rename(columns=ren), hide_index=True)
    if not df.empty:
        csv_btn(df.rename(columns=ren), "⬇️ تصدير السجل (CSV)", "invoices.csv", "h_csv")
        no = st.selectbox("عرض / طباعة / مشاركة فاتورة", df["invoice_no"].tolist(), key="h_sel")
        show_invoice(no, "hist")

def page_reports():
    head("📊", "التقارير التفصيلية", "تحليلات المبيعات والمخزون مع إمكانية التصدير")
    c1, c2 = st.columns(2)
    br = c1.selectbox("الفرع", ["كل الفروع"] + BRANCHES, key="rp_br")
    period = c2.radio("الفترة", PERIODS, horizontal=True, key="rp_p")
    pc, pp = period_clause(period)
    bc, bp = branch_clause(br)
    t1, t2, t3, t4, t5, t6 = st.tabs(["المبيعات حسب الماركة/المنشأ", "أفضل الأصناف مبيعاً", "حالة المخزون", "النواقص",
                                      "الخصومات والعروض", "المرتجعات"])
    with t1:
        bo = qdf(f"""SELECT brand, quality_origin, SUM(qty) pieces, SUM(amount) net, SUM(profit) profit FROM v_movements
            WHERE 1=1{pc}{bc} GROUP BY brand, quality_origin ORDER BY net DESC""", pp + bp)
        if bo.empty:
            st.info("لا توجد حركة.")
        else:
            out = bo.rename(columns={"brand": "الماركة", "quality_origin": "المنشأ", "pieces": "القطع (صافي)", "net": "صافي المبيعات", "profit": "الربح"})
            st.dataframe(out, hide_index=True)
            st.bar_chart(bo.assign(l=bo["brand"] + " - " + bo["quality_origin"]).set_index("l")[["net", "profit"]])
            csv_btn(out, "⬇️ تصدير (CSV)", "sales_by_brand.csv", "rp_c1")
    with t2:
        tp = qdf(f"""SELECT name, model, SUM(qty) pieces, SUM(amount) net FROM v_movements WHERE 1=1{pc}{bc}
            GROUP BY name, model HAVING pieces>0 ORDER BY pieces DESC LIMIT 20""", pp + bp)
        out = tp.rename(columns={"name": "الصنف", "model": "الموديل", "pieces": "القطع (صافي)", "net": "صافي المبيعات"})
        st.dataframe(out, hide_index=True)
        if not tp.empty:
            csv_btn(out, "⬇️ تصدير (CSV)", "top_items.csv", "rp_c2")
    with t3:
        st_df = qdf(f"""SELECT branch, quality_origin, COUNT(*) items, SUM(quantity) pieces, SUM(quantity*selling_price) val
            FROM inventory WHERE 1=1{bc} GROUP BY branch, quality_origin ORDER BY branch""", bp)
        out = st_df.rename(columns={"branch": "الفرع", "quality_origin": "المنشأ", "items": "الأصناف", "pieces": "القطع", "val": "القيمة (بيع)"})
        st.dataframe(out, hide_index=True)
        csv_btn(out, "⬇️ تصدير (CSV)", "stock_status.csv", "rp_c3")
    with t4:
        lim = st.number_input("حد النواقص (أقل من)", min_value=1, value=low_limit(), step=1, key="rp_lim")
        lw = qdf(f"SELECT {INV_COLS} FROM inventory WHERE quantity<?{bc} ORDER BY quantity, branch", [int(lim)] + bp)
        out = show(lw).drop(columns=["م"])
        st.caption(f"عدد الأصناف الناقصة: {len(out)}")
        st.dataframe(out, hide_index=True)
        if not out.empty:
            csv_btn(out, "⬇️ تصدير قائمة النواقص (CSV)", "low_stock.csv", "rp_c4")
    with t5:
        bd = qdf(f"""SELECT branch, SUM(amount+disc) gross_list, SUM(disc) disc FROM v_movements
            WHERE kind='sale'{pc}{bc} GROUP BY branch""", pp + bp)
        st.dataframe(bd.rename(columns={"branch": "الفرع", "gross_list": "المبيعات قبل الخصم", "disc": "الخصومات الممنوحة"}), hide_index=True)
        st.subheader("الخصومات حسب العرض/النوع")
        nt = qdf(f"""SELECT discount_note, COUNT(*) lines, SUM(qty*(COALESCE(NULLIF(list_price,0),unit_price)-unit_price)) disc
            FROM invoices WHERE discount_note<>''{pc}{bc} GROUP BY discount_note ORDER BY disc DESC""", pp + bp)
        out2 = nt.rename(columns={"discount_note": "العرض / نوع الخصم", "lines": "عدد البنود", "disc": "قيمة الخصم"})
        st.dataframe(out2, hide_index=True)
        if not nt.empty:
            csv_btn(out2, "⬇️ تصدير (CSV)", "discounts.csv", "rp_c5")
    with t6:
        rt = qdf(f"""SELECT return_no,date,invoice_no,branch,name,brand,qty,amount,reason FROM returns
            WHERE 1=1{pc}{bc} ORDER BY id DESC""", pp + bp)
        out3 = rt.rename(columns={"return_no": "رقم المرتجع", "date": "التاريخ", "invoice_no": "الفاتورة", "branch": "الفرع",
                                  "name": "الصنف", "brand": "الماركة", "qty": "الكمية", "amount": "المبلغ", "reason": "السبب"})
        st.metric("إجمالي المرتجعات في الفترة", egp(float(rt["amount"].sum()) if not rt.empty else 0))
        st.dataframe(out3, hide_index=True)
        if not rt.empty:
            csv_btn(out3, "⬇️ تصدير (CSV)", "returns_report.csv", "rp_c6")

def db_backup_bytes():
    """نسخة احتياطية متسقة عبر sqlite backup API (آمنة حتى مع وضع WAL ووجود عمليات جارية)."""
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    src = conn()
    try:
        dst = sqlite3.connect(tmp)
        src.backup(dst)
        dst.close()
        return Path(tmp).read_bytes()
    finally:
        src.close()
        try:
            os.remove(tmp)
        except OSError:
            pass

def page_settings():
    head("⚙️", "الإعدادات", "بيانات المحل، حد النواقص والخصم، كلمة المرور، النسخ الاحتياطي، والبيانات التجريبية")
    st.subheader("بيانات المحل (تظهر في الفاتورة)")
    with st.form("store_form"):
        a, b = st.columns(2)
        name = a.text_input("اسم المحل", get_setting("store_name"))
        phone = b.text_input("هاتف المحل", get_setting("store_phone"))
        addr = a.text_input("العنوان", get_setting("store_address"))
        lim = b.number_input("حد تنبيه النواقص", min_value=1, value=low_limit(), step=1)
        mdisc = a.number_input("أقصى نسبة لإجمالي الخصم الفعلي على الفاتورة % (عروض + يدوي + فاتورة)", min_value=0, max_value=100,
                               value=int(max_discount()), step=1)
        if st.form_submit_button("حفظ الإعدادات", type="primary"):
            with tx() as c:
                for k, v in {"store_name": name.strip() or "قطع غيار مرسيدس", "store_phone": phone.strip(),
                             "store_address": addr.strip(), "low_limit": int(lim), "max_discount": int(mdisc)}.items():
                    _set(c, k, v)
            st.success("تم حفظ الإعدادات."); st.rerun()
    st.subheader("🔐 تغيير كلمة المرور")
    with st.form("pw_form", clear_on_submit=True):
        old, new, new2 = st.text_input("الحالية", type="password"), st.text_input("الجديدة (6 أحرف على الأقل)", type="password"), \
            st.text_input("تأكيد الجديدة", type="password")
        if st.form_submit_button("تغيير كلمة المرور"):
            ok, wait = login_attempt(old)   # نفس قفل السيرفر يحمي هذه الشاشة من التخمين
            if wait and not ok:
                st.error(f"محاولات خاطئة كثيرة. حاول بعد {wait} ثانية.")
            elif not ok:
                st.error("كلمة المرور الحالية غير صحيحة.")
            elif len(new) < 6 or new != new2:
                st.error("كلمة المرور الجديدة قصيرة أو غير متطابقة.")
            else:
                set_password(new); st.success("تم تغيير كلمة المرور.")
    st.subheader("💾 النسخ الاحتياطي والاستعادة")
    if Path(DB).exists():
        st.download_button("⬇️ تحميل نسخة احتياطية من قاعدة البيانات", db_backup_bytes(),
                           file_name=f"mercedes_parts_backup_{datetime.date.today()}.db", mime="application/octet-stream")
    up = st.file_uploader("استعادة من نسخة احتياطية (.db)", type=["db", "sqlite"])
    if up is not None and st.checkbox("أؤكد أن بيانات النظام الحالية ستُستبدل بالكامل"):
        if st.button("استعادة النسخة"):
            tmp = DB + ".tmp"
            Path(tmp).write_bytes(up.getvalue())
            try:
                t = sqlite3.connect(tmp)
                names = {r[0] for r in t.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                healthy = t.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
                t.close()
                if {"inventory", "invoices"} <= names and healthy:
                    for ext in ("-wal", "-shm"):   # ملفات WAL القديمة يجب ألا تختلط بالقاعدة المستعادة
                        if os.path.exists(DB + ext):
                            os.remove(DB + ext)
                    os.replace(tmp, DB); init_db()
                    st.success("تمت الاستعادة بنجاح (وتمت ترقية الهيكل تلقائياً عند الحاجة).")
                else:
                    os.remove(tmp); st.error("الملف ليس نسخة صالحة من النظام.")
            except sqlite3.DatabaseError:
                os.remove(tmp); st.error("الملف غير صالح.")
    # ✅ [تعديل 4] إدارة البيانات التجريبية والتصفير
    st.subheader("🧪 البيانات التجريبية والتصفير")
    n_demo = int(qdf("SELECT COUNT(*) c FROM inventory WHERE is_demo=1").iloc[0, 0])
    st.write(f"الأصناف التجريبية الحالية: **{n_demo}** — يُنصح بتحميل نسخة احتياطية قبل أي حذف.")
    if n_demo == 0 and st.button("📦 تحميل البيانات التجريبية (300 صنف)"):
        st.success(f"تم تحميل {load_demo()} صنف تجريبي."); st.rerun()
    if n_demo:
        ok1 = st.checkbox("أؤكد حذف الأصناف التجريبية", key="st_c1")
        if st.button("🧹 حذف الأصناف التجريبية", disabled=not ok1):
            gone, kept = purge_demo_items()
            st.success(f"تم حذف {gone} صنف تجريبي." + (f" (بقي {kept} صنف لارتباطه بفواتير؛ صفّر سجلات التشغيل أولاً لحذفه)" if kept else ""))
            st.rerun()
    st.markdown("**تصفير سجلات التشغيل** (الفواتير + المرتجعات + التحويلات، ويُبقي المخزون) — مفيد بعد انتهاء التجربة وقبل البدء الفعلي:")
    w1 = st.text_input("اكتب كلمة (تصفير) للتأكيد", key="st_w1")
    if st.button("🗑️ تصفير سجلات التشغيل", disabled=w1.strip() != "تصفير"):
        reset_operations()
        for k in ("cart", "last_invoice", "cart_branch"):
            st.session_state.pop(k, None)
        st.success("تم تصفير الفواتير والمرتجعات والتحويلات."); st.rerun()
    st.markdown("**تصفير كامل** (المخزون + العروض + كل السجلات، ويُبقي الإعدادات وكلمة المرور):")
    w2 = st.text_input("اكتب كلمة (حذف الكل) للتأكيد", key="st_w2")
    if st.button("⚠️ تصفير النظام بالكامل", disabled=w2.strip() != "حذف الكل"):
        reset_all()
        for k in ("cart", "last_invoice", "cart_branch"):
            st.session_state.pop(k, None)
        st.success("تم تصفير النظام بالكامل."); st.rerun()

def page_offers():
    head("🏷️", "العروض والخصومات", "أنشئ عروضاً تُطبَّق تلقائياً في شاشة المبيعات حسب الفرع والفترة والكمية")
    st.caption(f"الحد الأقصى لإجمالي الخصم الفعلي على الفاتورة حالياً {max_discount():g}% (يُغيَّر من الإعدادات). "
               "عند تطابق أكثر من عرض يُطبَّق الأفضل للعميل فقط (بدون تجميع).")
    today = datetime.date.today().isoformat()
    df = qdf("SELECT * FROM offers ORDER BY active DESC, id DESC")
    if df.empty:
        st.info("لا توجد عروض بعد. أنشئ أول عرض من النموذج بالأسفل.")
    else:
        def status(r):
            if not r["active"]:
                return "⏸️ متوقف"
            if r["start_date"] and r["start_date"] > today:
                return "⏳ قادم"
            if r["end_date"] and r["end_date"] < today:
                return "⌛ منتهي"
            return "✅ فعّال"
        view = df.assign(status=df.apply(status, axis=1)).drop(columns=["active"])
        st.dataframe(view.rename(columns={"id": "م", "name": "اسم العرض", "type": "نوع الخصم", "value": "القيمة", "scope": "ينطبق على",
                                          "scope_value": "قيمة النطاق", "branch": "الفرع", "min_qty": "أقل كمية",
                                          "start_date": "من", "end_date": "إلى", "status": "الحالة"}), hide_index=True)
        opts = {f"#{r['id']} {r['name']}": r for _, r in df.iterrows()}
        sel = opts[st.selectbox("إدارة عرض", list(opts.keys()), key="of_manage")]
        a, b, _ = st.columns([1, 1, 3])
        if a.button("⏯️ تفعيل / إيقاف"):
            run("UPDATE offers SET active=? WHERE id=?", (0 if sel["active"] else 1, int(sel["id"]))); st.rerun()
        if b.button("🗑️ حذف العرض"):
            run("DELETE FROM offers WHERE id=?", (int(sel["id"]),)); st.rerun()
    st.divider()
    st.subheader("➕ عرض جديد")
    name = st.text_input("اسم العرض (مثال: خصم الصيف على التيل)", key="of_name")
    c1, c2, c3 = st.columns(3)
    typ = c1.selectbox("نوع الخصم", OFFER_TYPES, key="of_type")
    val = c2.number_input("قيمة الخصم", min_value=0.0, value=10.0, step=1.0, key="of_val")
    minq = c3.number_input("أقل كمية لتطبيق العرض (للعروض الكمية)", min_value=1, value=1, step=1, key="of_minq")
    s1, s2 = st.columns(2)
    scope = s1.selectbox("ينطبق على", SCOPES, key="of_scope")
    sval = ""
    if scope == "فئة":
        sval = s2.selectbox("الفئة", qdf("SELECT DISTINCT category v FROM inventory ORDER BY v")["v"].tolist(), key="of_sv1")
    elif scope == "ماركة":
        sval = s2.selectbox("الماركة", qdf("SELECT DISTINCT brand v FROM inventory ORDER BY v")["v"].tolist(), key="of_sv2")
    elif scope == "منشأ/جودة":
        sval = s2.selectbox("المنشأ/الجودة", ORIGINS, key="of_sv3")
    elif scope == "موديل":
        sval = s2.selectbox("الموديل", qdf("SELECT DISTINCT model v FROM inventory ORDER BY v")["v"].tolist(), key="of_sv4")
    elif scope == "رقم OEM":
        sval = s2.text_input("رقم OEM أو بدايته (مثال: A20542)", key="of_sv5").strip()
    d1, d2, d3, d4 = st.columns(4)
    obr = d1.selectbox("الفرع", ["الكل"] + BRANCHES, key="of_br")
    start = d2.date_input("بداية العرض", value=datetime.date.today(), key="of_start")
    no_end = d3.checkbox("بدون تاريخ انتهاء", value=False, key="of_noend")
    end = d4.date_input("نهاية العرض", value=datetime.date.today() + datetime.timedelta(days=7), key="of_end", disabled=no_end)
    if typ == OFFER_TYPES[0] and val > max_discount():
        st.warning(f"⚠️ نسبة العرض ({val:g}%) أعلى من الحد المسموح للخصم ({max_discount():g}%) — سيُمنع البيع بهذا العرض إلا بعد رفع الحد من الإعدادات.")
    if st.button("💾 حفظ العرض", type="primary", key="of_save"):
        if not name.strip():
            st.error("اسم العرض مطلوب.")
        elif val <= 0 or (typ == OFFER_TYPES[0] and val > 100):
            st.error("قيمة الخصم غير صحيحة (النسبة بين 0 و100).")
        elif scope != "كل الأصناف" and not sval:
            st.error("حدد قيمة النطاق.")
        elif not no_end and end < start:
            st.error("تاريخ النهاية قبل البداية.")
        else:
            run("""INSERT INTO offers(name,type,value,scope,scope_value,branch,min_qty,start_date,end_date,active)
                VALUES (?,?,?,?,?,?,?,?,?,1)""", (name.strip(), typ, float(val), scope, sval, obr, int(minq),
                                                  start.isoformat(), "" if no_end else end.isoformat()))
            st.success("تم حفظ العرض وسيُطبَّق تلقائياً في المبيعات."); st.rerun()

LABEL_CSS = """<style>.lbs{display:flex;flex-wrap:wrap;gap:3mm;direction:rtl;font-family:Tahoma,Arial,sans-serif}
.lb{width:60mm;border:1px dashed #999;padding:2mm;text-align:center;page-break-inside:avoid;background:#fff;color:#111}
.lb svg{max-width:100%;height:auto}.ln{font-size:11px;font-weight:700;line-height:1.25}.lm{font-size:10px;color:#444}
.lp{font-size:12px;font-weight:700}.lp span{font-size:10px;color:#555;margin-right:6px}
.btn{padding:8px 20px;font-size:15px;background:#1e88e5;color:#fff;border:0;border-radius:8px;cursor:pointer;margin:6px 0}
@media print{.np{display:none!important}@page{margin:6mm}}</style>"""

def labels_html(rows, copies, by_qty):
    cells, skipped = "", []
    for r in rows:
        code = str(r["barcode"] or "")
        if not valid_ean13(code):
            skipped.append(r["part_number"]); continue
        n = min(100, max(1, int(r["quantity"])) if by_qty else int(copies))
        cell = (f'<div class="lb"><div class="ln">{html.escape(str(r["name"])[:42])}</div>'
                f'<div class="lm">{html.escape(str(r["model"]))} | {html.escape(str(r["brand"]))}</div>{ean13_svg(code)}'
                f'<div class="lp">{r["selling_price"]:,.0f} ج.م<span>{html.escape(str(r["location"] or ""))}</span></div></div>')
        cells += cell * n
    page = (LABEL_CSS + '<button class="btn np" onclick="window.print()">🖨️ طباعة الملصقات</button>'
            f'<div class="lbs">{cells}</div>')
    return page, skipped

def page_barcode():
    head("🔖", "الباركود", "طباعة ملصقات الباركود وتعيين باركود مخصص — ويُمسح مباشرة في شاشة المبيعات والبحث")
    t1, t2 = st.tabs(["🖨️ طباعة الملصقات", "✏️ تعيين / تعديل باركود"])
    with t1:
        c1, c2 = st.columns(2)
        br = c1.selectbox("الفرع", ["الكل"] + BRANCHES, key="bc_br")
        q = c2.text_input("🔍 بحث عن الأصناف", key="bc_q")
        df = search_inv(q, br).head(300)
        opts = {f"{r['part_number']} | {r['name']} | {r['model']} | {r['brand']} | {r['branch']}": r for _, r in df.iterrows()}
        all_res = st.checkbox("اختيار كل نتائج البحث الحالية (حتى 60 صنف)", key="bc_all")
        picked = [] if all_res else st.multiselect("اختر الأصناف", list(opts.keys()), key="bc_pick")
        x1, x2 = st.columns(2)
        copies = x1.number_input("عدد الملصقات لكل صنف", min_value=1, max_value=100, value=1, step=1, key="bc_copies")
        by_qty = x2.checkbox("عدد الملصقات = الكمية الموجودة بالمخزن", key="bc_byqty")
        rows = list(opts.values())[:60] if all_res else [opts[k] for k in picked]
        if rows:
            page, skipped = labels_html(rows, copies, by_qty)
            if skipped:
                st.warning("لا يمكن رسم ملصق لهذه الأصناف لأن باركودها المخصص ليس EAN-13: " + " ، ".join(skipped[:8]))
            components.html(page, height=560, scrolling=True)
            full = f'<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8"><title>Barcodes</title></head><body>{page}</body></html>'
            st.download_button("⬇️ تحميل الملصقات (HTML)", full, file_name="barcode_labels.html", mime="text/html", key="bc_dl")
        else:
            st.info("اختر أصنافاً لعرض الملصقات.")
    with t2:
        q2 = st.text_input("🔍 ابحث عن الصنف", key="bc_q2")
        df2 = search_inv(q2).head(100)
        if df2.empty:
            st.info("لا توجد نتائج.")
        else:
            opts2 = {f"{r['part_number']} | {r['name']} | {r['model']} | {r['brand']} | {r['branch']} | باركود: {r['barcode']}": r
                     for _, r in df2.iterrows()}
            r = opts2[st.selectbox("الصنف", list(opts2.keys()), key="bc_item")]
            vk = (str(r["part_number"]), str(r["brand"]), str(r["quality_origin"]))   # الباركود لكل منتج (يشمل كل الفروع)
            st.write(f"الباركود الحالي: **{r['barcode']}** — " + ("✅ EAN-13 قابل للطباعة" if valid_ean13(r["barcode"]) else "⚠️ غير EAN-13 (يُمسح فقط، لا يُرسم)"))
            new = st.text_input("الباركود الجديد (كما هو مطبوع على العبوة، بدون مسافات)", key="bc_new").strip()
            a, b = st.columns(2)
            if a.button("💾 حفظ الباركود", type="primary"):
                if not new or " " in new:
                    st.error("أدخل باركوداً صحيحاً بدون مسافات.")
                elif not qdf(f"SELECT 1 FROM inventory WHERE barcode=? AND NOT ({VARIANT_SQL})", (new,) + vk).empty:
                    st.error("هذا الباركود مستخدم لمنتج آخر!")
                else:
                    run(f"UPDATE inventory SET barcode=? WHERE {VARIANT_SQL}", (new,) + vk)
                    st.success("تم تحديث الباركود (لكل فروع هذا المنتج)."); st.rerun()
            if b.button("🔄 إعادة توليد الباركود الداخلي"):
                run(f"UPDATE inventory SET barcode=? WHERE {VARIANT_SQL}", (internal_barcode(r["id"]),) + vk)
                st.success("تمت إعادة التوليد."); st.rerun()

# ============================================================== الدخول والتشغيل
def login_screen():
    _, mid, _ = st.columns([1, 1.2, 1])
    with mid:
        st.markdown(f'<div class="login-card"><div style="font-size:3rem">🚗</div><h2>{html.escape(get_setting("store_name"))}</h2>'
                    f'<p>نظام إدارة المخازن والمبيعات — تسجيل الدخول</p></div>', unsafe_allow_html=True)
        wait = float(get_setting("lock_until", "0") or 0) - time.time()   # ✅ [تعديل 6] القفل مخزَّن في القاعدة (عام)
        if wait > 0:
            st.error(f"النظام مقفل مؤقتاً بسبب محاولات دخول خاطئة. حاول بعد {int(wait) + 1} ثانية."); return
        with st.form("login"):
            pw = st.text_input("كلمة المرور", type="password")
            go = st.form_submit_button("دخول", type="primary")
        if go:
            ok, wait = login_attempt(pw)
            if ok:
                st.session_state["auth"] = True; st.rerun()
            elif wait:
                st.error(f"محاولات خاطئة كثيرة. تم قفل الدخول لمدة {wait} ثانية.")
            else:
                st.error("كلمة المرور غير صحيحة.")

st.set_page_config(page_title="نظام مخازن مرسيدس", page_icon="🚗", layout="wide")
st.markdown(CSS, unsafe_allow_html=True)
ensure_ready()
if not st.session_state.get("auth"):
    login_screen()
    st.stop()
if get_setting("setup_done") != "1":
    first_run_screen()
    st.stop()

PAGES = {"📈 لوحة التحكم": page_dashboard, "🔍 البحث الذكي": page_search, "🧾 المبيعات (POS)": page_pos,
         "🏷️ العروض والخصومات": page_offers, "📦 إدارة المخزون": page_inventory, "🔖 الباركود": page_barcode,
         "🔄 تحويل المخزون": page_transfer, "↩️ المرتجعات": page_returns, "🗂️ سجل الفواتير": page_history,
         "📊 التقارير": page_reports, "⚙️ الإعدادات": page_settings}
with st.sidebar:
    st.markdown(f'<div class="brand">🚗 {html.escape(get_setting("store_name"))}<small>نظام المخازن والمبيعات</small></div>', unsafe_allow_html=True)
    choice = st.radio("القائمة", list(PAGES.keys()), label_visibility="collapsed")
    st.divider()
    if st.button("🚪 تسجيل الخروج"):
        st.session_state.clear(); st.rerun()
    st.caption(datetime.date.today().strftime("%Y-%m-%d"))
PAGES[choice]()
