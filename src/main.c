#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <sodium.h>
#include <sqlite3.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include <jansson.h>
#include <microhttpd.h>

#include "docs/docs_ui.h"
#include "http/response.h"
#include "http/routes_meta.h"

#define DEFAULT_PORT 8080
#define DEFAULT_DB_PATH "./data/app.db"
#define DEFAULT_KEY_FILE "./data/user_key.b64"
#define DEFAULT_SESSION_TTL_HOURS 12
#define DEFAULT_ADMIN_USERNAME "admin"
#define DEFAULT_ADMIN_PASSWORD "Admin@123456"

#define MAX_BODY_SIZE (1024 * 1024)
#define RAW_TOKEN_BYTES 32
#define TOKEN_HASH_HEX_LEN (crypto_generichash_BYTES * 2)

typedef struct {
    int port;
    int session_ttl_hours;
    const char *db_path;
    const char *key_file;
} ServerConfig;

typedef struct {
    int user_id;
    char username[128];
    char role[32];
} AuthUser;

static ServerConfig g_cfg;
static sqlite3 *g_db = NULL;
static pthread_mutex_t g_db_mutex = PTHREAD_MUTEX_INITIALIZER;
static unsigned char g_user_key[crypto_secretbox_KEYBYTES];
static volatile sig_atomic_t g_running = 1;

static void handle_signal(int sig) {
    (void)sig;
    g_running = 0;
}

static char *dup_cstr(const char *src) {
    if (src == NULL) {
        return NULL;
    }
    const size_t len = strlen(src);
    char *dst = (char *)malloc(len + 1);
    if (dst == NULL) {
        return NULL;
    }
    memcpy(dst, src, len + 1);
    return dst;
}

static int env_to_int(const char *name, int fallback) {
    const char *v = getenv(name);
    if (v == NULL || *v == '\0') {
        return fallback;
    }

    char *end = NULL;
    errno = 0;
    long n = strtol(v, &end, 10);
    if (errno != 0 || end == v || *end != '\0' || n <= 0 || n > INT_MAX) {
        return fallback;
    }
    return (int)n;
}

static void bytes_to_hex(const unsigned char *in, size_t in_len, char *out) {
    static const char hex[] = "0123456789abcdef";
    for (size_t i = 0; i < in_len; ++i) {
        out[i * 2] = hex[(in[i] >> 4) & 0x0F];
        out[i * 2 + 1] = hex[in[i] & 0x0F];
    }
    out[in_len * 2] = '\0';
}

static int hash_token(const char *token, char out_hex[TOKEN_HASH_HEX_LEN + 1]) {
    unsigned char hash[crypto_generichash_BYTES];
    if (crypto_generichash(hash, sizeof(hash), (const unsigned char *)token,
                           strlen(token), NULL, 0) != 0) {
        return -1;
    }
    bytes_to_hex(hash, sizeof(hash), out_hex);
    return 0;
}

static int generate_access_token(char *out, size_t out_size) {
    const size_t needed =
        sodium_base64_encoded_len(RAW_TOKEN_BYTES,
                                  sodium_base64_VARIANT_URLSAFE_NO_PADDING);
    if (out_size < needed) {
        return -1;
    }

    unsigned char raw[RAW_TOKEN_BYTES];
    randombytes_buf(raw, sizeof(raw));
    sodium_bin2base64(out, out_size, raw, sizeof(raw),
                      sodium_base64_VARIANT_URLSAFE_NO_PADDING);
    return 0;
}

static time_t now_epoch(void) { return time(NULL); }

static int ensure_parent_dir(const char *path) {
    if (path == NULL) {
        return -1;
    }

    char *copy = dup_cstr(path);
    if (copy == NULL) {
        return -1;
    }

    for (char *p = copy + 1; *p != '\0'; ++p) {
        if (*p == '/') {
            *p = '\0';
            if (mkdir(copy, 0755) != 0 && errno != EEXIST) {
                free(copy);
                return -1;
            }
            *p = '/';
        }
    }

    free(copy);
    return 0;
}

static int load_or_create_key(void) {
    const char *env_key = getenv("USER_DATA_KEY_B64");
    if (env_key != NULL && *env_key != '\0') {
        size_t bin_len = 0;
        if (sodium_base642bin(g_user_key, sizeof(g_user_key), env_key,
                              strlen(env_key), NULL, &bin_len, NULL,
                              sodium_base64_VARIANT_ORIGINAL) == 0 &&
            bin_len == sizeof(g_user_key)) {
            return 0;
        }
        fprintf(stderr,
                "[WARN] USER_DATA_KEY_B64 无效，将尝试从密钥文件加载。\n");
    }

    FILE *f = fopen(g_cfg.key_file, "rb");
    if (f != NULL) {
        char line[256];
        if (fgets(line, sizeof(line), f) != NULL) {
            line[strcspn(line, "\r\n")] = '\0';
            size_t bin_len = 0;
            if (sodium_base642bin(g_user_key, sizeof(g_user_key), line,
                                  strlen(line), NULL, &bin_len, NULL,
                                  sodium_base64_VARIANT_ORIGINAL) == 0 &&
                bin_len == sizeof(g_user_key)) {
                fclose(f);
                return 0;
            }
        }
        fclose(f);
    }

    randombytes_buf(g_user_key, sizeof(g_user_key));
    const size_t enc_len = sodium_base64_encoded_len(
        sizeof(g_user_key), sodium_base64_VARIANT_ORIGINAL);
    char *b64 = (char *)malloc(enc_len + 2);
    if (b64 == NULL) {
        return -1;
    }

    sodium_bin2base64(b64, enc_len + 2, g_user_key, sizeof(g_user_key),
                      sodium_base64_VARIANT_ORIGINAL);

    if (ensure_parent_dir(g_cfg.key_file) != 0) {
        free(b64);
        return -1;
    }

    f = fopen(g_cfg.key_file, "wb");
    if (f == NULL) {
        free(b64);
        return -1;
    }

    fprintf(f, "%s\n", b64);
    fclose(f);
    chmod(g_cfg.key_file, 0600);
    free(b64);

    fprintf(stdout,
            "[INFO] 已自动生成新的用户字段加密密钥: %s\n"
            "[INFO] 请妥善备份该文件，丢失后将无法解密已有用户信息。\n",
            g_cfg.key_file);

    return 0;
}

static int encrypt_text(const char *plain, char **out_b64) {
    if (plain == NULL) {
        plain = "";
    }

    const size_t plain_len = strlen(plain);
    const size_t boxed_len = crypto_secretbox_NONCEBYTES +
                             crypto_secretbox_MACBYTES + plain_len;

    unsigned char *boxed = (unsigned char *)malloc(boxed_len);
    if (boxed == NULL) {
        return -1;
    }

    unsigned char *nonce = boxed;
    unsigned char *cipher = boxed + crypto_secretbox_NONCEBYTES;
    randombytes_buf(nonce, crypto_secretbox_NONCEBYTES);

    if (crypto_secretbox_easy(cipher, (const unsigned char *)plain, plain_len,
                              nonce, g_user_key) != 0) {
        free(boxed);
        return -1;
    }

    const size_t enc_len =
        sodium_base64_encoded_len(boxed_len, sodium_base64_VARIANT_ORIGINAL);
    char *b64 = (char *)malloc(enc_len + 1);
    if (b64 == NULL) {
        free(boxed);
        return -1;
    }

    sodium_bin2base64(b64, enc_len + 1, boxed, boxed_len,
                      sodium_base64_VARIANT_ORIGINAL);

    free(boxed);
    *out_b64 = b64;
    return 0;
}

static int decrypt_text(const char *b64, char **out_plain) {
    if (b64 == NULL || *b64 == '\0') {
        *out_plain = dup_cstr("");
        return *out_plain == NULL ? -1 : 0;
    }

    const size_t max_len = strlen(b64) * 3 / 4 + 4;
    unsigned char *boxed = (unsigned char *)malloc(max_len);
    if (boxed == NULL) {
        return -1;
    }

    size_t boxed_len = 0;
    if (sodium_base642bin(boxed, max_len, b64, strlen(b64), NULL, &boxed_len,
                          NULL, sodium_base64_VARIANT_ORIGINAL) != 0) {
        free(boxed);
        return -1;
    }

    if (boxed_len <
        crypto_secretbox_NONCEBYTES + crypto_secretbox_MACBYTES) {
        free(boxed);
        return -1;
    }

    const unsigned char *nonce = boxed;
    const unsigned char *cipher = boxed + crypto_secretbox_NONCEBYTES;
    const size_t cipher_len = boxed_len - crypto_secretbox_NONCEBYTES;
    const size_t plain_len = cipher_len - crypto_secretbox_MACBYTES;

    unsigned char *plain = (unsigned char *)malloc(plain_len + 1);
    if (plain == NULL) {
        free(boxed);
        return -1;
    }

    if (crypto_secretbox_open_easy(plain, cipher, cipher_len, nonce,
                                   g_user_key) != 0) {
        free(boxed);
        free(plain);
        return -1;
    }

    plain[plain_len] = '\0';
    free(boxed);
    *out_plain = (char *)plain;
    return 0;
}

static int db_exec(const char *sql) {
    char *err = NULL;
    const int rc = sqlite3_exec(g_db, sql, NULL, NULL, &err);
    if (rc != SQLITE_OK) {
        if (err != NULL) {
            fprintf(stderr, "[DB] SQL执行失败: %s\n", err);
            sqlite3_free(err);
        }
        return -1;
    }
    return 0;
}

static int db_init(void) {
    if (ensure_parent_dir(g_cfg.db_path) != 0) {
        fprintf(stderr, "[DB] 无法创建数据库目录: %s\n", g_cfg.db_path);
        return -1;
    }

    if (sqlite3_open_v2(g_cfg.db_path, &g_db,
                        SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE |
                            SQLITE_OPEN_FULLMUTEX,
                        NULL) != SQLITE_OK) {
        fprintf(stderr, "[DB] 打开数据库失败: %s\n", sqlite3_errmsg(g_db));
        return -1;
    }

    sqlite3_busy_timeout(g_db, 5000);

    const char *schema_sql =
        "PRAGMA foreign_keys = ON;"
        "PRAGMA journal_mode = WAL;"
        "PRAGMA synchronous = NORMAL;"

        "CREATE TABLE IF NOT EXISTS users ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  username TEXT NOT NULL UNIQUE,"
        "  password_hash TEXT NOT NULL,"
        "  role TEXT NOT NULL CHECK(role IN ('admin','staff')),"
        "  full_name_enc TEXT,"
        "  email_enc TEXT,"
        "  phone_enc TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS sessions ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  user_id INTEGER NOT NULL,"
        "  token_hash TEXT NOT NULL UNIQUE,"
        "  expires_at INTEGER NOT NULL,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE"
        ");"

        "CREATE TABLE IF NOT EXISTS products ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  sku TEXT NOT NULL UNIQUE,"
        "  name TEXT NOT NULL,"
        "  unit TEXT NOT NULL DEFAULT '瓶',"
        "  stock_quantity INTEGER NOT NULL DEFAULT 0 CHECK(stock_quantity >= 0),"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS stock_movements ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  product_id INTEGER NOT NULL,"
        "  movement_type TEXT NOT NULL CHECK(movement_type IN ('IN','OUT')),"
        "  quantity INTEGER NOT NULL CHECK(quantity > 0),"
        "  unit_price_cents INTEGER NOT NULL CHECK(unit_price_cents >= 0),"
        "  note TEXT,"
        "  operator_user_id INTEGER NOT NULL,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(product_id) REFERENCES products(id),"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS machines ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  machine_code TEXT NOT NULL UNIQUE,"
        "  location TEXT NOT NULL,"
        "  status TEXT NOT NULL DEFAULT 'online' CHECK(status IN ('online','offline','downtime')),"
        "  door_error INTEGER NOT NULL DEFAULT 0 CHECK(door_error IN (0,1)),"
        "  temp_celsius REAL NOT NULL DEFAULT 4.0,"
        "  temp_alert INTEGER NOT NULL DEFAULT 0 CHECK(temp_alert IN (0,1)),"
        "  temp_min REAL NOT NULL DEFAULT 0.0,"
        "  temp_max REAL NOT NULL DEFAULT 8.0,"
        "  estimated_hourly_sales_cents INTEGER NOT NULL DEFAULT 0,"
        "  priority_weight INTEGER NOT NULL DEFAULT 50 CHECK(priority_weight BETWEEN 0 AND 100),"
        "  note TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP"
        ");"

        "CREATE TABLE IF NOT EXISTS machine_stock ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  machine_id INTEGER NOT NULL,"
        "  product_id INTEGER NOT NULL,"
        "  stock_quantity INTEGER NOT NULL DEFAULT 0 CHECK(stock_quantity >= 0),"
        "  capacity INTEGER NOT NULL DEFAULT 50 CHECK(capacity > 0),"
        "  restock_threshold INTEGER NOT NULL DEFAULT 10 CHECK(restock_threshold >= 0),"
        "  last_restock_at TEXT,"
        "  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(machine_id) REFERENCES machines(id) ON DELETE CASCADE,"
        "  FOREIGN KEY(product_id) REFERENCES products(id),"
        "  UNIQUE(machine_id, product_id)"
        ");"

        "CREATE TABLE IF NOT EXISTS machine_sales ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  machine_id INTEGER NOT NULL,"
        "  product_id INTEGER NOT NULL,"
        "  quantity INTEGER NOT NULL CHECK(quantity > 0),"
        "  unit_price_cents INTEGER NOT NULL CHECK(unit_price_cents >= 0),"
        "  total_amount_cents INTEGER NOT NULL CHECK(total_amount_cents >= 0),"
        "  payment_method TEXT NOT NULL CHECK(payment_method IN ('cash','scan','other')),"
        "  note TEXT,"
        "  operator_user_id INTEGER,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(machine_id) REFERENCES machines(id),"
        "  FOREIGN KEY(product_id) REFERENCES products(id),"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS machine_downtime ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  machine_id INTEGER NOT NULL,"
        "  start_time TEXT NOT NULL,"
        "  end_time TEXT,"
        "  duration_minutes INTEGER,"
        "  reason TEXT NOT NULL,"
        "  estimated_loss_cents INTEGER NOT NULL DEFAULT 0,"
        "  resolved INTEGER NOT NULL DEFAULT 0 CHECK(resolved IN (0,1)),"
        "  note TEXT,"
        "  resolution_note TEXT,"
        "  operator_user_id INTEGER,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(machine_id) REFERENCES machines(id),"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS replenishment_routes ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  route_date TEXT NOT NULL,"
        "  operator_user_id INTEGER,"
        "  status TEXT NOT NULL DEFAULT 'pending' CHECK(status IN ('pending','in_progress','completed','cancelled')),"
        "  total_machines INTEGER NOT NULL DEFAULT 0,"
        "  completed_machines INTEGER NOT NULL DEFAULT 0,"
        "  note TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS replenishment_route_items ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  route_id INTEGER NOT NULL,"
        "  machine_id INTEGER NOT NULL,"
        "  priority_score INTEGER NOT NULL DEFAULT 0,"
        "  sort_order INTEGER NOT NULL DEFAULT 0,"
        "  status TEXT NOT NULL DEFAULT 'pending' CHECK(status IN ('pending','skipped','completed')),"
        "  low_stock_reason TEXT,"
        "  door_error INTEGER NOT NULL DEFAULT 0,"
        "  temp_alert INTEGER NOT NULL DEFAULT 0,"
        "  estimated_products_needed INTEGER NOT NULL DEFAULT 0,"
        "  actual_products_restocked INTEGER NOT NULL DEFAULT 0,"
        "  note TEXT,"
        "  completed_at TEXT,"
        "  FOREIGN KEY(route_id) REFERENCES replenishment_routes(id) ON DELETE CASCADE,"
        "  FOREIGN KEY(machine_id) REFERENCES machines(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS daily_reports ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  report_date TEXT NOT NULL UNIQUE,"
        "  total_sales_cents INTEGER NOT NULL DEFAULT 0,"
        "  cash_sales_cents INTEGER NOT NULL DEFAULT 0,"
        "  scan_sales_cents INTEGER NOT NULL DEFAULT 0,"
        "  other_sales_cents INTEGER NOT NULL DEFAULT 0,"
        "  total_transactions INTEGER NOT NULL DEFAULT 0,"
        "  total_quantity_sold INTEGER NOT NULL DEFAULT 0,"
        "  total_downtime_loss_cents INTEGER NOT NULL DEFAULT 0,"
        "  total_downtime_minutes INTEGER NOT NULL DEFAULT 0,"
        "  expected_cash_cents INTEGER NOT NULL DEFAULT 0,"
        "  actual_cash_cents INTEGER NOT NULL DEFAULT 0,"
        "  cash_difference_cents INTEGER NOT NULL DEFAULT 0,"
        "  expected_scan_cents INTEGER NOT NULL DEFAULT 0,"
        "  actual_scan_cents INTEGER NOT NULL DEFAULT 0,"
        "  scan_difference_cents INTEGER NOT NULL DEFAULT 0,"
        "  total_discrepancy_cents INTEGER NOT NULL DEFAULT 0,"
        "  discrepancy_note TEXT,"
        "  machines_online INTEGER NOT NULL DEFAULT 0,"
        "  machines_offline INTEGER NOT NULL DEFAULT 0,"
        "  machines_in_downtime INTEGER NOT NULL DEFAULT 0,"
        "  machines_with_door_errors INTEGER NOT NULL DEFAULT 0,"
        "  machines_with_temp_alerts INTEGER NOT NULL DEFAULT 0,"
        "  note TEXT,"
        "  operator_user_id INTEGER,"
        "  reconciled INTEGER NOT NULL DEFAULT 0 CHECK(reconciled IN (0,1)),"
        "  reconciled_at TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE TABLE IF NOT EXISTS shift_reconciliations ("
        "  id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "  shift_date TEXT NOT NULL,"
        "  shift_type TEXT NOT NULL CHECK(shift_type IN ('morning','afternoon','evening','night','daily')),"
        "  operator_user_id INTEGER NOT NULL,"
        "  expected_cash_cents INTEGER NOT NULL DEFAULT 0,"
        "  actual_cash_cents INTEGER NOT NULL DEFAULT 0,"
        "  cash_difference_cents INTEGER NOT NULL DEFAULT 0,"
        "  expected_scan_cents INTEGER NOT NULL DEFAULT 0,"
        "  actual_scan_cents INTEGER NOT NULL DEFAULT 0,"
        "  scan_difference_cents INTEGER NOT NULL DEFAULT 0,"
        "  expected_other_cents INTEGER NOT NULL DEFAULT 0,"
        "  actual_other_cents INTEGER NOT NULL DEFAULT 0,"
        "  other_difference_cents INTEGER NOT NULL DEFAULT 0,"
        "  total_discrepancy_cents INTEGER NOT NULL DEFAULT 0,"
        "  discrepancy_reason TEXT,"
        "  note TEXT,"
        "  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,"
        "  FOREIGN KEY(operator_user_id) REFERENCES users(id)"
        ");"

        "CREATE INDEX IF NOT EXISTS idx_sessions_token_hash ON sessions(token_hash);"
        "CREATE INDEX IF NOT EXISTS idx_sessions_expires_at ON sessions(expires_at);"
        "CREATE INDEX IF NOT EXISTS idx_products_sku ON products(sku);"
        "CREATE INDEX IF NOT EXISTS idx_movements_product_id ON "
        "stock_movements(product_id);"
        "CREATE INDEX IF NOT EXISTS idx_movements_created_at ON "
        "stock_movements(created_at);"

        "CREATE INDEX IF NOT EXISTS idx_machines_code ON machines(machine_code);"
        "CREATE INDEX IF NOT EXISTS idx_machines_status ON machines(status);"
        "CREATE INDEX IF NOT EXISTS idx_machines_door_error ON machines(door_error);"
        "CREATE INDEX IF NOT EXISTS idx_machines_temp_alert ON machines(temp_alert);"

        "CREATE INDEX IF NOT EXISTS idx_machine_stock_machine_id ON machine_stock(machine_id);"
        "CREATE INDEX IF NOT EXISTS idx_machine_stock_product_id ON machine_stock(product_id);"
        "CREATE INDEX IF NOT EXISTS idx_machine_stock_low ON machine_stock(stock_quantity, restock_threshold);"

        "CREATE INDEX IF NOT EXISTS idx_machine_sales_machine_id ON machine_sales(machine_id);"
        "CREATE INDEX IF NOT EXISTS idx_machine_sales_product_id ON machine_sales(product_id);"
        "CREATE INDEX IF NOT EXISTS idx_machine_sales_created ON machine_sales(created_at);"
        "CREATE INDEX IF NOT EXISTS idx_machine_sales_payment ON machine_sales(payment_method);"

        "CREATE INDEX IF NOT EXISTS idx_downtime_machine_id ON machine_downtime(machine_id);"
        "CREATE INDEX IF NOT EXISTS idx_downtime_start ON machine_downtime(start_time);"
        "CREATE INDEX IF NOT EXISTS idx_downtime_resolved ON machine_downtime(resolved);"

        "CREATE INDEX IF NOT EXISTS idx_routes_date ON replenishment_routes(route_date);"
        "CREATE INDEX IF NOT EXISTS idx_routes_status ON replenishment_routes(status);"
        "CREATE INDEX IF NOT EXISTS idx_route_items_route_id ON replenishment_route_items(route_id);"
        "CREATE INDEX IF NOT EXISTS idx_route_items_machine_id ON replenishment_route_items(machine_id);"

        "CREATE INDEX IF NOT EXISTS idx_daily_reports_date ON daily_reports(report_date);"
        "CREATE INDEX IF NOT EXISTS idx_daily_reports_reconciled ON daily_reports(reconciled);"
        "CREATE INDEX IF NOT EXISTS idx_shift_rec_date ON shift_reconciliations(shift_date);"
        "CREATE INDEX IF NOT EXISTS idx_shift_rec_operator ON shift_reconciliations(operator_user_id);"

        "INSERT OR IGNORE INTO products (sku, name, unit, stock_quantity) VALUES "
        "('SEED-WATER-550', '系统示例矿泉水550ml', '瓶', 50);";

    if (db_exec(schema_sql) != 0) {
        return -1;
    }

    if (db_exec("ALTER TABLE machine_downtime ADD COLUMN note TEXT;") != 0) {
        sqlite3_exec(g_db, "COMMIT;", NULL, NULL, NULL);
    }

    return 0;
}

static int append_body(ConnectionInfo *ci, const char *data, size_t size) {
    if (size == 0) {
        return 0;
    }
    if (ci->body_size + size > MAX_BODY_SIZE) {
        return -1;
    }

    char *new_buf = (char *)realloc(ci->body, ci->body_size + size + 1);
    if (new_buf == NULL) {
        return -1;
    }

    ci->body = new_buf;
    memcpy(ci->body + ci->body_size, data, size);
    ci->body_size += size;
    ci->body[ci->body_size] = '\0';
    return 0;
}

static int is_method_with_body(const char *method) {
    return strcmp(method, MHD_HTTP_METHOD_POST) == 0 ||
           strcmp(method, MHD_HTTP_METHOD_PUT) == 0 ||
           strcmp(method, MHD_HTTP_METHOD_PATCH) == 0;
}

static int parse_json_body(ConnectionInfo *ci, json_t **out,
                           char err_msg[256]) {
    if (ci->body_size == 0) {
        snprintf(err_msg, 256, "请求体不能为空");
        return -1;
    }

    json_error_t jerr;
    json_t *obj = json_loadb(ci->body, ci->body_size, 0, &jerr);
    if (obj == NULL || !json_is_object(obj)) {
        if (obj != NULL) {
            json_decref(obj);
        }
        snprintf(err_msg, 256, "JSON 格式错误: %s", jerr.text);
        return -1;
    }

    *out = obj;
    return 0;
}

static const char *safe_col_text(sqlite3_stmt *stmt, int col) {
    const unsigned char *text = sqlite3_column_text(stmt, col);
    return text == NULL ? "" : (const char *)text;
}

static int db_user_count(int *count_out) {
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(g_db, "SELECT COUNT(*) FROM users;", -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        return -1;
    }

    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        return -1;
    }

    *count_out = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);
    return 0;
}

static int ensure_default_admin_user(void) {
    int user_count = 0;
    if (db_user_count(&user_count) != 0) {
        fprintf(stderr, "[DB] 查询用户数量失败，无法初始化默认管理员\n");
        return -1;
    }
    if (user_count > 0) {
        return 0;
    }

    const char *admin_username = getenv("DEFAULT_ADMIN_USERNAME");
    if (admin_username == NULL || *admin_username == '\0') {
        admin_username = DEFAULT_ADMIN_USERNAME;
    }

    const char *admin_password = getenv("DEFAULT_ADMIN_PASSWORD");
    if (admin_password == NULL || *admin_password == '\0') {
        admin_password = DEFAULT_ADMIN_PASSWORD;
    }

    char password_hash[crypto_pwhash_STRBYTES];
    if (crypto_pwhash_str(password_hash, admin_password, strlen(admin_password),
                          crypto_pwhash_OPSLIMIT_INTERACTIVE,
                          crypto_pwhash_MEMLIMIT_INTERACTIVE) != 0) {
        fprintf(stderr, "[SECURITY] 默认管理员密码哈希失败\n");
        return -1;
    }

    char *full_name_enc = NULL;
    char *email_enc = NULL;
    char *phone_enc = NULL;
    if (encrypt_text("系统管理员", &full_name_enc) != 0 ||
        encrypt_text("admin@local", &email_enc) != 0 ||
        encrypt_text("", &phone_enc) != 0) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        fprintf(stderr, "[SECURITY] 默认管理员信息加密失败\n");
        return -1;
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO users (username, password_hash, role, full_name_enc, "
        "email_enc, phone_enc) VALUES (?, ?, 'admin', ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        fprintf(stderr, "[DB] 默认管理员插入预编译失败\n");
        return -1;
    }

    sqlite3_bind_text(stmt, 1, admin_username, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, password_hash, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, full_name_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 4, email_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 5, phone_enc, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    free(full_name_enc);
    free(email_enc);
    free(phone_enc);

    if (rc != SQLITE_DONE) {
        fprintf(stderr, "[DB] 默认管理员创建失败\n");
        return -1;
    }

    fprintf(stdout,
            "[INFO] 已初始化默认管理员账号: %s\n"
            "[INFO] 默认管理员密码可通过环境变量 DEFAULT_ADMIN_PASSWORD 覆盖\n",
            admin_username);
    return 0;
}

static int ensure_seed_stock_movement_consistency(void) {
    sqlite3_stmt *stmt = NULL;
    int admin_user_id = 0;
    int rc = sqlite3_prepare_v2(
        g_db, "SELECT id FROM users WHERE role='admin' ORDER BY id LIMIT 1;", -1,
        &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 查询管理员失败，无法修复种子库存流水\n");
        return -1;
    }
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        admin_user_id = sqlite3_column_int(stmt, 0);
    }
    sqlite3_finalize(stmt);
    if (admin_user_id <= 0) {
        return 0;
    }

    int product_id = 0;
    int stock_quantity = 0;
    rc = sqlite3_prepare_v2(
        g_db, "SELECT id, stock_quantity FROM products WHERE sku=? LIMIT 1;", -1,
        &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 查询种子商品失败，无法修复种子库存流水\n");
        return -1;
    }
    sqlite3_bind_text(stmt, 1, "SEED-WATER-550", -1, SQLITE_STATIC);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        product_id = sqlite3_column_int(stmt, 0);
        stock_quantity = sqlite3_column_int(stmt, 1);
    }
    sqlite3_finalize(stmt);
    if (product_id <= 0) {
        return 0;
    }

    int in_total = 0;
    int out_total = 0;
    rc = sqlite3_prepare_v2(
        g_db,
        "SELECT "
        "COALESCE(SUM(CASE WHEN movement_type='IN' THEN quantity ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN movement_type='OUT' THEN quantity ELSE 0 END), 0) "
        "FROM stock_movements WHERE product_id=?;",
        -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 查询种子商品流水失败，无法修复种子库存流水\n");
        return -1;
    }
    sqlite3_bind_int(stmt, 1, product_id);
    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        fprintf(stderr, "[DB] 读取种子商品流水失败，无法修复种子库存流水\n");
        return -1;
    }
    in_total = sqlite3_column_int(stmt, 0);
    out_total = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    if (in_total > 0) {
        return 0;
    }

    int inferred_initial_in = stock_quantity + out_total;
    if (inferred_initial_in <= 0) {
        return 0;
    }

    rc = sqlite3_prepare_v2(
        g_db,
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'IN', ?, 0, '系统初始化库存补录', ?);",
        -1, &stmt, NULL);
    if (rc != SQLITE_OK) {
        fprintf(stderr, "[DB] 补录种子库存流水预编译失败\n");
        return -1;
    }
    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, inferred_initial_in);
    sqlite3_bind_int(stmt, 3, admin_user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        fprintf(stderr, "[DB] 补录种子库存流水失败\n");
        return -1;
    }

    fprintf(stdout, "[INFO] 已修复种子商品库存流水: sku=SEED-WATER-550, in=%d\n",
            inferred_initial_in);
    return 0;
}

static int authenticate_request(struct MHD_Connection *connection,
                                AuthUser *out_user,
                                char token_hash_hex[TOKEN_HASH_HEX_LEN + 1]) {
    const char *auth_header =
        MHD_lookup_connection_value(connection, MHD_HEADER_KIND, "Authorization");
    if (auth_header == NULL || strncmp(auth_header, "Bearer ", 7) != 0) {
        return 0;
    }

    const char *token = auth_header + 7;
    if (*token == '\0') {
        return 0;
    }

    if (hash_token(token, token_hash_hex) != 0) {
        return 0;
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT u.id, u.username, u.role "
        "FROM sessions s "
        "JOIN users u ON u.id = s.user_id "
        "WHERE s.token_hash = ? AND s.expires_at > ? "
        "LIMIT 1;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        return 0;
    }

    sqlite3_bind_text(stmt, 1, token_hash_hex, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt, 2, (sqlite3_int64)now_epoch());

    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        return 0;
    }

    out_user->user_id = sqlite3_column_int(stmt, 0);
    snprintf(out_user->username, sizeof(out_user->username), "%s",
             safe_col_text(stmt, 1));
    snprintf(out_user->role, sizeof(out_user->role), "%s", safe_col_text(stmt, 2));

    sqlite3_finalize(stmt);
    return 1;
}

static int is_admin_role(const AuthUser *user) {
    return strcmp(user->role, "admin") == 0;
}

static int parse_int_field(json_t *obj, const char *key, int min, int max,
                           int *out) {
    json_t *v = json_object_get(obj, key);
    if (!json_is_integer(v)) {
        return -1;
    }

    json_int_t n = json_integer_value(v);
    if (n < min || n > max) {
        return -1;
    }

    *out = (int)n;
    return 0;
}

static int require_string_field(json_t *obj, const char *key, size_t max_len,
                                const char **out) {
    json_t *v = json_object_get(obj, key);
    if (!json_is_string(v)) {
        return -1;
    }

    const char *s = json_string_value(v);
    if (s == NULL) {
        return -1;
    }

    size_t len = strlen(s);
    if (len == 0 || len > max_len) {
        return -1;
    }

    *out = s;
    return 0;
}

static const char *optional_string_field(json_t *obj, const char *key,
                                         size_t max_len) {
    json_t *v = json_object_get(obj, key);
    if (v == NULL || json_is_null(v)) {
        return "";
    }
    if (!json_is_string(v)) {
        return NULL;
    }

    const char *s = json_string_value(v);
    if (s == NULL || strlen(s) > max_len) {
        return NULL;
    }
    return s;
}

static enum MHD_Result handle_health(struct MHD_Connection *connection) {
    json_t *data = json_object();
    json_object_set_new(data, "service", json_string("jinxiaocun-backend-c"));
    json_object_set_new(data, "status", json_string("ok"));
    json_object_set_new(data, "timestamp", json_integer((json_int_t)now_epoch()));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_register(struct MHD_Connection *connection,
                                       ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *username = NULL;
    const char *password = NULL;
    if (require_string_field(body, "username", 64, &username) != 0 ||
        require_string_field(body, "password", 128, &password) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "username/password 必填，且长度必须合法");
    }

    const char *full_name = optional_string_field(body, "full_name", 128);
    const char *email = optional_string_field(body, "email", 128);
    const char *phone = optional_string_field(body, "phone", 64);
    if (full_name == NULL || email == NULL || phone == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "full_name/email/phone 必须是字符串且长度合法");
    }

    const char *role_input = optional_string_field(body, "role", 16);
    if (role_input == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "role 必须是字符串");
    }

    pthread_mutex_lock(&g_db_mutex);

    int user_count = 0;
    if (db_user_count(&user_count) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询用户数量失败");
    }

    AuthUser creator;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    const int first_user = (user_count == 0);
    if (!first_user) {
        if (!authenticate_request(connection, &creator, token_hash)) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_UNAUTHORIZED,
                                "UNAUTHORIZED", "需要管理员身份创建用户");
        }
        if (!is_admin_role(&creator)) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                                "仅管理员可创建用户");
        }
    }

    const char *role = "staff";
    if (first_user) {
        role = "admin";
    } else if (role_input != NULL && *role_input != '\0') {
        if (strcmp(role_input, "admin") != 0 && strcmp(role_input, "staff") != 0) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_BAD_REQUEST,
                                "INVALID_INPUT", "role 仅支持 admin/staff");
        }
        role = role_input;
    }

    char username_copy[65];
    char role_copy[17];
    snprintf(username_copy, sizeof(username_copy), "%s", username);
    snprintf(role_copy, sizeof(role_copy), "%s", role);

    char password_hash[crypto_pwhash_STRBYTES];
    if (crypto_pwhash_str(password_hash, password, strlen(password),
                          crypto_pwhash_OPSLIMIT_INTERACTIVE,
                          crypto_pwhash_MEMLIMIT_INTERACTIVE) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "密码加密失败");
    }

    char *full_name_enc = NULL;
    char *email_enc = NULL;
    char *phone_enc = NULL;
    if (encrypt_text(full_name, &full_name_enc) != 0 ||
        encrypt_text(email, &email_enc) != 0 ||
        encrypt_text(phone, &phone_enc) != 0) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "用户信息加密失败");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO users (username, password_hash, role, full_name_enc, "
        "email_enc, phone_enc) VALUES (?, ?, ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        free(full_name_enc);
        free(email_enc);
        free(phone_enc);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建用户预编译失败");
    }

    sqlite3_bind_text(stmt, 1, username_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, password_hash, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, role_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 4, full_name_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 5, email_enc, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 6, phone_enc, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    free(full_name_enc);
    free(email_enc);
    free(phone_enc);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "用户名已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建用户失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "username", json_string(username_copy));
    json_object_set_new(data, "role", json_string(role_copy));
    json_object_set_new(data, "first_user", first_user ? json_true() : json_false());
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_login(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *username = NULL;
    const char *password = NULL;
    if (require_string_field(body, "username", 64, &username) != 0 ||
        require_string_field(body, "password", 128, &password) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "username/password 必填");
    }

    char username_copy[65];
    snprintf(username_copy, sizeof(username_copy), "%s", username);

    pthread_mutex_lock(&g_db_mutex);

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, password_hash, role FROM users WHERE username = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "数据库查询失败");
    }

    sqlite3_bind_text(stmt, 1, username, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "用户名或密码错误");
    }

    int user_id = sqlite3_column_int(stmt, 0);
    const char *password_hash = safe_col_text(stmt, 1);
    char role_copy[32];
    snprintf(role_copy, sizeof(role_copy), "%s", safe_col_text(stmt, 2));

    if (crypto_pwhash_str_verify(password_hash, password, strlen(password)) != 0) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "用户名或密码错误");
    }
    sqlite3_finalize(stmt);

    char token[128] = {0};
    if (generate_access_token(token, sizeof(token)) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "生成令牌失败");
    }

    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (hash_token(token, token_hash) != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "处理令牌失败");
    }

    const time_t expires_at = now_epoch() + (time_t)g_cfg.session_ttl_hours * 3600;

    if (db_exec("DELETE FROM sessions WHERE expires_at <= strftime('%s', 'now');") != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "会话清理失败");
    }

    const char *insert_sql =
        "INSERT INTO sessions (user_id, token_hash, expires_at) VALUES (?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, insert_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "会话创建失败");
    }

    sqlite3_bind_int(stmt, 1, user_id);
    sqlite3_bind_text(stmt, 2, token_hash, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt, 3, (sqlite3_int64)expires_at);

    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "会话创建失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "access_token", json_string(token));
    json_object_set_new(data, "token_type", json_string("Bearer"));
    json_object_set_new(data, "expires_at", json_integer((json_int_t)expires_at));
    json_object_set_new(data, "user_id", json_integer(user_id));
    json_object_set_new(data, "username", json_string(username_copy));
    json_object_set_new(data, "role", json_string(role_copy));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_logout(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "未登录或令牌无效");
    }

    sqlite3_stmt *stmt = NULL;
    if (sqlite3_prepare_v2(g_db, "DELETE FROM sessions WHERE token_hash = ?;", -1,
                           &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "退出登录失败");
    }

    sqlite3_bind_text(stmt, 1, token_hash, -1, SQLITE_TRANSIENT);
    sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    pthread_mutex_unlock(&g_db_mutex);

    json_t *data = json_object();
    json_object_set_new(data, "message", json_string("已退出登录"));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_auth_me(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "未登录或令牌无效");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT full_name_enc, email_enc, phone_enc, created_at "
        "FROM users WHERE id = ? LIMIT 1;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询用户详情失败");
    }

    sqlite3_bind_int(stmt, 1, user.user_id);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "用户不存在");
    }

    const char *full_name_enc = safe_col_text(stmt, 0);
    const char *email_enc = safe_col_text(stmt, 1);
    const char *phone_enc = safe_col_text(stmt, 2);
    char created_at[64];
    snprintf(created_at, sizeof(created_at), "%s", safe_col_text(stmt, 3));

    char *full_name = NULL;
    char *email = NULL;
    char *phone = NULL;

    int ok = decrypt_text(full_name_enc, &full_name) == 0 &&
             decrypt_text(email_enc, &email) == 0 &&
             decrypt_text(phone_enc, &phone) == 0;

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (!ok) {
        free(full_name);
        free(email);
        free(phone);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "SECURITY_ERROR", "解密用户信息失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "user_id", json_integer(user.user_id));
    json_object_set_new(data, "username", json_string(user.username));
    json_object_set_new(data, "role", json_string(user.role));
    json_object_set_new(data, "full_name", json_string(full_name));
    json_object_set_new(data, "email", json_string(email));
    json_object_set_new(data, "phone", json_string(phone));
    json_object_set_new(data, "created_at", json_string(created_at));

    free(full_name);
    free(email);
    free(phone);

    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_create_product(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    const char *name = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0 ||
        require_string_field(body, "name", 128, &name) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku/name 必填");
    }

    const char *unit = optional_string_field(body, "unit", 16);
    if (unit == NULL || *unit == '\0') {
        unit = "瓶";
    }

    char sku_copy[65];
    char name_copy[129];
    char unit_copy[17];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);
    snprintf(name_copy, sizeof(name_copy), "%s", name);
    snprintf(unit_copy, sizeof(unit_copy), "%s", unit);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可新增商品");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO products (sku, name, unit, stock_quantity) VALUES (?, ?, ?, 0);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增商品失败");
    }

    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, name_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, unit_copy, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "商品 SKU 已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增商品失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "name", json_string(name_copy));
    json_object_set_new(data, "unit", json_string(unit_copy));
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_list_products(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, sku, name, unit, stock_quantity, created_at, updated_at "
        "FROM products ORDER BY id DESC;";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品列表失败");
    }

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *item = json_object();
        json_object_set_new(item, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(item, "sku", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(item, "name", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(item, "unit", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(item, "stock_quantity",
                            json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(item, "created_at", json_string(safe_col_text(stmt, 5)));
        json_object_set_new(item, "updated_at", json_string(safe_col_text(stmt, 6)));
        json_array_append_new(items, item);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取商品列表失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static int begin_transaction(void) {
    return db_exec("BEGIN IMMEDIATE TRANSACTION;");
}

static void rollback_transaction(void) { db_exec("ROLLBACK;"); }

static int commit_transaction(void) { return db_exec("COMMIT;"); }

static enum MHD_Result handle_inbound(struct MHD_Connection *connection,
                                      ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku 必填");
    }

    int quantity = 0;
    int unit_cost = 0;
    if (parse_int_field(body, "quantity", 1, 1000000, &quantity) != 0 ||
        parse_int_field(body, "unit_cost_cents", 0, 100000000, &unit_cost) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity/unit_cost_cents 必须为合法整数");
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char sku_copy[65];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int product_id = 0;
    int current_stock = 0;

    const char *find_sql =
        "SELECT id, stock_quantity FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }

    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }

    product_id = sqlite3_column_int(stmt, 0);
    current_stock = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    const int new_stock = current_stock + quantity;

    const char *update_sql =
        "UPDATE products SET stock_quantity = ?, updated_at = CURRENT_TIMESTAMP "
        "WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    sqlite3_bind_int(stmt, 1, new_stock);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    const char *ins_sql =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'IN', ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, ins_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }

    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, quantity);
    sqlite3_bind_int(stmt, 3, unit_cost);
    sqlite3_bind_text(stmt, 4, note, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, user.user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交入库事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "movement_type", json_string("IN"));
    json_object_set_new(data, "quantity", json_integer(quantity));
    json_object_set_new(data, "new_stock", json_integer(new_stock));
    json_object_set_new(data, "operator", json_string(user.username));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_sales(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *sku = NULL;
    if (require_string_field(body, "sku", 64, &sku) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "sku 必填");
    }

    int quantity = 0;
    int sale_price = 0;
    if (parse_int_field(body, "quantity", 1, 1000000, &quantity) != 0 ||
        parse_int_field(body, "unit_price_cents", 0, 100000000, &sale_price) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity/unit_price_cents 必须为合法整数");
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char sku_copy[65];
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int product_id = 0;
    int current_stock = 0;

    const char *find_sql =
        "SELECT id, stock_quantity FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }

    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }

    product_id = sqlite3_column_int(stmt, 0);
    current_stock = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    if (current_stock < quantity) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "INSUFFICIENT_STOCK",
                            "库存不足，无法出库");
    }

    const int new_stock = current_stock - quantity;

    const char *update_sql =
        "UPDATE products SET stock_quantity = ?, updated_at = CURRENT_TIMESTAMP "
        "WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    sqlite3_bind_int(stmt, 1, new_stock);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    const char *ins_sql =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'OUT', ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, ins_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入流水失败");
    }

    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, quantity);
    sqlite3_bind_int(stmt, 3, sale_price);
    sqlite3_bind_text(stmt, 4, note, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 5, user.user_id);

    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交出库事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "movement_type", json_string("OUT"));
    json_object_set_new(data, "quantity", json_integer(quantity));
    json_object_set_new(data, "new_stock", json_integer(new_stock));
    json_object_set_new(data, "operator", json_string(user.username));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_inventory(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    sqlite3_stmt *summary_stmt = NULL;
    const char *summary_sql =
        "SELECT "
        "  (SELECT COUNT(*) FROM products),"
        "  (SELECT COALESCE(SUM(stock_quantity), 0) FROM products),"
        "  (SELECT COALESCE(SUM(quantity), 0) FROM stock_movements WHERE "
        "movement_type='IN'),"
        "  (SELECT COALESCE(SUM(quantity), 0) FROM stock_movements WHERE "
        "movement_type='OUT');";

    if (sqlite3_prepare_v2(g_db, summary_sql, -1, &summary_stmt, NULL) !=
        SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存汇总失败");
    }

    int rc = sqlite3_step(summary_stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(summary_stmt);
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存汇总失败");
    }

    int product_count = sqlite3_column_int(summary_stmt, 0);
    int total_stock = sqlite3_column_int(summary_stmt, 1);
    int total_in = sqlite3_column_int(summary_stmt, 2);
    int total_out = sqlite3_column_int(summary_stmt, 3);
    sqlite3_finalize(summary_stmt);

    sqlite3_stmt *list_stmt = NULL;
    const char *list_sql =
        "SELECT sku, name, unit, stock_quantity, updated_at "
        "FROM products ORDER BY stock_quantity DESC, id ASC;";
    if (sqlite3_prepare_v2(g_db, list_sql, -1, &list_stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存明细失败");
    }

    json_t *products = json_array();
    while ((rc = sqlite3_step(list_stmt)) == SQLITE_ROW) {
        json_t *item = json_object();
        json_object_set_new(item, "sku", json_string(safe_col_text(list_stmt, 0)));
        json_object_set_new(item, "name", json_string(safe_col_text(list_stmt, 1)));
        json_object_set_new(item, "unit", json_string(safe_col_text(list_stmt, 2)));
        json_object_set_new(item, "stock_quantity",
                            json_integer(sqlite3_column_int(list_stmt, 3)));
        json_object_set_new(item, "updated_at",
                            json_string(safe_col_text(list_stmt, 4)));
        json_array_append_new(products, item);
    }

    sqlite3_finalize(list_stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(products);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取库存明细失败");
    }

    json_t *data = json_object();
    json_t *summary = json_object();
    json_object_set_new(summary, "product_count", json_integer(product_count));
    json_object_set_new(summary, "total_stock_quantity", json_integer(total_stock));
    json_object_set_new(summary, "total_in_quantity", json_integer(total_in));
    json_object_set_new(summary, "total_out_quantity", json_integer(total_out));

    json_object_set_new(data, "summary", summary);
    json_object_set_new(data, "products", products);

    return respond_success(connection, MHD_HTTP_OK, data);
}

static int parse_limit_query(struct MHD_Connection *connection) {
    const char *limit_s =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "limit");
    if (limit_s == NULL || *limit_s == '\0') {
        return 50;
    }

    char *end = NULL;
    errno = 0;
    long v = strtol(limit_s, &end, 10);
    if (errno != 0 || end == limit_s || *end != '\0') {
        return 50;
    }
    if (v < 1) {
        v = 1;
    }
    if (v > 200) {
        v = 200;
    }
    return (int)v;
}

static enum MHD_Result handle_movements(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    const char *type =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "type");
    int use_type = 0;
    if (type != NULL && *type != '\0') {
        if (strcmp(type, "IN") == 0 || strcmp(type, "OUT") == 0) {
            use_type = 1;
        } else {
            pthread_mutex_unlock(&g_db_mutex);
            return respond_error(connection, MHD_HTTP_BAD_REQUEST,
                                "INVALID_INPUT", "type 仅支持 IN 或 OUT");
        }
    }

    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_all =
        "SELECT m.id, p.sku, p.name, m.movement_type, m.quantity, "
        "m.unit_price_cents, m.note, u.username, m.created_at "
        "FROM stock_movements m "
        "JOIN products p ON p.id = m.product_id "
        "JOIN users u ON u.id = m.operator_user_id "
        "ORDER BY m.id DESC LIMIT ?;";

    const char *sql_type =
        "SELECT m.id, p.sku, p.name, m.movement_type, m.quantity, "
        "m.unit_price_cents, m.note, u.username, m.created_at "
        "FROM stock_movements m "
        "JOIN products p ON p.id = m.product_id "
        "JOIN users u ON u.id = m.operator_user_id "
        "WHERE m.movement_type = ? "
        "ORDER BY m.id DESC LIMIT ?;";

    if (sqlite3_prepare_v2(g_db, use_type ? sql_type : sql_all, -1, &stmt, NULL) !=
        SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询流水失败");
    }

    int idx = 1;
    if (use_type) {
        sqlite3_bind_text(stmt, idx++, type, -1, SQLITE_TRANSIENT);
    }
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "sku", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "product_name", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "movement_type", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "quantity", json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(it, "unit_price_cents",
                            json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(it, "note", json_string(safe_col_text(stmt, 6)));
        json_object_set_new(it, "operator", json_string(safe_col_text(stmt, 7)));
        json_object_set_new(it, "created_at", json_string(safe_col_text(stmt, 8)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取流水失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_create_machine(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *machine_code = NULL;
    const char *location = NULL;
    if (require_string_field(body, "machine_code", 64, &machine_code) != 0 ||
        require_string_field(body, "location", 256, &location) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "machine_code/location 必填");
    }

    const char *status = optional_string_field(body, "status", 16);
    if (status == NULL || *status == '\0') { status = "online"; }
    if (strcmp(status, "online") != 0 && strcmp(status, "offline") != 0 &&
        strcmp(status, "downtime") != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "status 仅支持 online/offline/downtime");
    }

    int door_error = 0;
    int temp_alert = 0;
    int priority_weight = 50;
    double temp_celsius = 4.0;
    double temp_min = 0.0;
    double temp_max = 8.0;
    int estimated_hourly_sales_cents = 0;

    json_t *v = json_object_get(body, "door_error");
    if (json_is_boolean(v)) {
        door_error = json_boolean_value(v) ? 1 : 0;
    } else if (json_is_integer(v)) {
        door_error = json_integer_value(v) != 0 ? 1 : 0;
    }

    v = json_object_get(body, "temp_alert");
    if (json_is_boolean(v)) {
        temp_alert = json_boolean_value(v) ? 1 : 0;
    } else if (json_is_integer(v)) {
        temp_alert = json_integer_value(v) != 0 ? 1 : 0;
    }

    v = json_object_get(body, "priority_weight");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0 && n <= 100) { priority_weight = (int)n; }
    }

    v = json_object_get(body, "temp_celsius");
    if (json_is_number(v)) { temp_celsius = json_real_value(v); }

    v = json_object_get(body, "temp_min");
    if (json_is_number(v)) { temp_min = json_real_value(v); }

    v = json_object_get(body, "temp_max");
    if (json_is_number(v)) { temp_max = json_real_value(v); }

    v = json_object_get(body, "estimated_hourly_sales_cents");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) { estimated_hourly_sales_cents = (int)n; }
    }

    const char *note = optional_string_field(body, "note", 512);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过512字符");
    }

    char machine_code_copy[65];
    char location_copy[257];
    char status_copy[17];
    char note_copy[513];
    snprintf(machine_code_copy, sizeof(machine_code_copy), "%s", machine_code);
    snprintf(location_copy, sizeof(location_copy), "%s", location);
    snprintf(status_copy, sizeof(status_copy), "%s", status);
    snprintf(note_copy, sizeof(note_copy), "%s", note);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可新增售货机");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "INSERT INTO machines (machine_code, location, status, door_error, "
        "temp_celsius, temp_alert, temp_min, temp_max, estimated_hourly_sales_cents, "
        "priority_weight, note) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);";

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增售货机失败");
    }

    sqlite3_bind_text(stmt, 1, machine_code_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, location_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 3, status_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 4, door_error);
    sqlite3_bind_double(stmt, 5, temp_celsius);
    sqlite3_bind_int(stmt, 6, temp_alert);
    sqlite3_bind_double(stmt, 7, temp_min);
    sqlite3_bind_double(stmt, 8, temp_max);
    sqlite3_bind_int(stmt, 9, estimated_hourly_sales_cents);
    sqlite3_bind_int(stmt, 10, priority_weight);
    sqlite3_bind_text(stmt, 11, note_copy, -1, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        if (rc == SQLITE_CONSTRAINT) {
            return respond_error(connection, MHD_HTTP_CONFLICT, "CONFLICT",
                                "售货机编号已存在");
        }
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "新增售货机失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "machine_code", json_string(machine_code_copy));
    json_object_set_new(data, "location", json_string(location_copy));
    json_object_set_new(data, "status", json_string(status_copy));
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_list_machines(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *status_filter =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "status");
    const char *has_error =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "has_error");

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT id, machine_code, location, status, door_error, temp_celsius, "
        "temp_alert, temp_min, temp_max, estimated_hourly_sales_cents, "
        "priority_weight, note, created_at, updated_at FROM machines ";

    char sql[1024];
    int use_status = 0;
    int use_error = 0;
    const char *status_val = NULL;
    const char *error_val = NULL;

    if (status_filter != NULL && *status_filter != '\0' &&
        (strcmp(status_filter, "online") == 0 || strcmp(status_filter, "offline") == 0 ||
         strcmp(status_filter, "downtime") == 0)) {
        use_status = 1;
        status_val = status_filter;
    }

    if (has_error != NULL && *has_error != '\0' &&
        (strcmp(has_error, "door") == 0 || strcmp(has_error, "temp") == 0 ||
         strcmp(has_error, "any") == 0)) {
        use_error = 1;
        error_val = has_error;
    }

    if (use_status || use_error) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_status) {
            strcat(sql, "status = ? ");
            first = 0;
        }
        if (use_error) {
            if (!first) strcat(sql, "AND ");
            if (strcmp(error_val, "door") == 0) {
                strcat(sql, "door_error = 1 ");
            } else if (strcmp(error_val, "temp") == 0) {
                strcat(sql, "temp_alert = 1 ");
            } else {
                strcat(sql, "(door_error = 1 OR temp_alert = 1) ");
            }
        }
        strcat(sql, "ORDER BY priority_weight DESC, id ASC;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY priority_weight DESC, id ASC;", sql_base);
    }

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询售货机列表失败");
    }

    int idx = 1;
    if (use_status) {
        sqlite3_bind_text(stmt, idx++, status_val, -1, SQLITE_TRANSIENT);
    }

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *item = json_object();
        json_object_set_new(item, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(item, "machine_code", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(item, "location", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(item, "status", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(item, "door_error",
                            json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(item, "temp_celsius",
                            json_real(sqlite3_column_double(stmt, 5)));
        json_object_set_new(item, "temp_alert",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(item, "temp_min",
                            json_real(sqlite3_column_double(stmt, 7)));
        json_object_set_new(item, "temp_max",
                            json_real(sqlite3_column_double(stmt, 8)));
        json_object_set_new(item, "estimated_hourly_sales_cents",
                            json_integer(sqlite3_column_int(stmt, 9)));
        json_object_set_new(item, "priority_weight",
                            json_integer(sqlite3_column_int(stmt, 10)));
        json_object_set_new(item, "note", json_string(safe_col_text(stmt, 11)));
        json_object_set_new(item, "created_at", json_string(safe_col_text(stmt, 12)));
        json_object_set_new(item, "updated_at", json_string(safe_col_text(stmt, 13)));
        json_array_append_new(items, item);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取售货机列表失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_update_machine(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *machine_code = NULL;
    if (require_string_field(body, "machine_code", 64, &machine_code) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "machine_code 必填");
    }

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    sqlite3_stmt *stmt = NULL;
    int machine_id = 0;
    int current_door_error = 0;
    int current_temp_alert = 0;
    double current_temp = 4.0;
    char current_status[32] = {0};

    const char *find_sql =
        "SELECT id, status, door_error, temp_celsius, temp_alert "
        "FROM machines WHERE machine_code = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询售货机失败");
    }
    sqlite3_bind_text(stmt, 1, machine_code, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "售货机不存在");
    }
    machine_id = sqlite3_column_int(stmt, 0);
    snprintf(current_status, sizeof(current_status), "%s", safe_col_text(stmt, 1));
    current_door_error = sqlite3_column_int(stmt, 2);
    current_temp = sqlite3_column_double(stmt, 3);
    current_temp_alert = sqlite3_column_int(stmt, 4);
    sqlite3_finalize(stmt);

    const char *location = optional_string_field(body, "location", 256);
    const char *status = optional_string_field(body, "status", 16);
    const char *note = optional_string_field(body, "note", 512);

    if (location == NULL || status == NULL || note == NULL) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "location/status/note 需为合法字符串");
    }

    if (status != NULL && *status != '\0') {
        if (strcmp(status, "online") != 0 && strcmp(status, "offline") != 0 &&
            strcmp(status, "downtime") != 0) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                                "status 仅支持 online/offline/downtime");
        }
    }

    char new_location[257];
    char new_status[17];
    char new_note[513];
    snprintf(new_location, sizeof(new_location), "%s",
             location != NULL && *location != '\0' ? location : "");
    snprintf(new_status, sizeof(new_status), "%s",
             status != NULL && *status != '\0' ? status : current_status);
    snprintf(new_note, sizeof(new_note), "%s",
             note != NULL ? note : "");

    int door_error = current_door_error;
    int temp_alert = current_temp_alert;
    int priority_weight = -1;
    double temp_celsius = current_temp;
    double temp_min = -1.0;
    double temp_max = -1.0;
    int estimated_hourly_sales_cents = -1;

    json_t *v = json_object_get(body, "door_error");
    if (json_is_boolean(v)) {
        door_error = json_boolean_value(v) ? 1 : 0;
    } else if (json_is_integer(v)) {
        door_error = json_integer_value(v) != 0 ? 1 : 0;
    }

    v = json_object_get(body, "temp_alert");
    if (json_is_boolean(v)) {
        temp_alert = json_boolean_value(v) ? 1 : 0;
    } else if (json_is_integer(v)) {
        temp_alert = json_integer_value(v) != 0 ? 1 : 0;
    }

    v = json_object_get(body, "priority_weight");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0 && n <= 100) { priority_weight = (int)n; }
    }

    v = json_object_get(body, "temp_celsius");
    if (json_is_number(v)) { temp_celsius = json_real_value(v); }

    v = json_object_get(body, "temp_min");
    if (json_is_number(v)) { temp_min = json_real_value(v); }

    v = json_object_get(body, "temp_max");
    if (json_is_number(v)) { temp_max = json_real_value(v); }

    v = json_object_get(body, "estimated_hourly_sales_cents");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) { estimated_hourly_sales_cents = (int)n; }
    }

    const char *update_sql =
        "UPDATE machines SET location = ?, status = ?, door_error = ?, "
        "temp_celsius = ?, temp_alert = ?, priority_weight = ?, note = ?, "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, update_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新售货机预编译失败");
    }

    sqlite3_bind_text(stmt, 1, new_location, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, new_status, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 3, door_error);
    sqlite3_bind_double(stmt, 4, temp_celsius);
    sqlite3_bind_int(stmt, 5, temp_alert);
    sqlite3_bind_int(stmt, 6, priority_weight >= 0 ? priority_weight : 50);
    sqlite3_bind_text(stmt, 7, new_note, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 8, machine_id);

    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (temp_min >= 0.0 || temp_max >= 0.0 || estimated_hourly_sales_cents >= 0) {
        char update_sql2[512];
        int first = 0;
        strcpy(update_sql2, "UPDATE machines SET ");
        if (temp_min >= 0.0) {
            strcat(update_sql2, "temp_min = ?");
            first = 1;
        }
        if (temp_max >= 0.0) {
            if (first) strcat(update_sql2, ", ");
            strcat(update_sql2, "temp_max = ?");
            first = 1;
        }
        if (estimated_hourly_sales_cents >= 0) {
            if (first) strcat(update_sql2, ", ");
            strcat(update_sql2, "estimated_hourly_sales_cents = ?");
        }
        strcat(update_sql2, " WHERE id = ?;");

        if (sqlite3_prepare_v2(g_db, update_sql2, -1, &stmt, NULL) != SQLITE_OK) {
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "更新售货机附加字段失败");
        }
        int idx2 = 1;
        if (temp_min >= 0.0) sqlite3_bind_double(stmt, idx2++, temp_min);
        if (temp_max >= 0.0) sqlite3_bind_double(stmt, idx2++, temp_max);
        if (estimated_hourly_sales_cents >= 0)
            sqlite3_bind_int(stmt, idx2++, estimated_hourly_sales_cents);
        sqlite3_bind_int(stmt, idx2, machine_id);
        sqlite3_step(stmt);
        sqlite3_finalize(stmt);
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新售货机失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "machine_code", json_string(machine_code));
    json_object_set_new(data, "status", json_string(new_status));
    json_object_set_new(data, "door_error", json_integer(door_error));
    json_object_set_new(data, "temp_alert", json_integer(temp_alert));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_delete_machine(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *machine_code = NULL;
    if (require_string_field(body, "machine_code", 64, &machine_code) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "machine_code 必填");
    }

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可删除售货机");
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql = "DELETE FROM machines WHERE machine_code = ?;";
    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "删除售货机失败");
    }

    sqlite3_bind_text(stmt, 1, machine_code, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    int changes = sqlite3_changes(g_db);
    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "删除售货机失败");
    }

    if (changes == 0) {
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "售货机不存在");
    }

    json_t *data = json_object();
    json_object_set_new(data, "message", json_string("删除成功"));
    json_object_set_new(data, "machine_code", json_string(machine_code));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_machine_stock_add(struct MHD_Connection *connection,
                                                ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *machine_code = NULL;
    const char *sku = NULL;
    if (require_string_field(body, "machine_code", 64, &machine_code) != 0 ||
        require_string_field(body, "sku", 64, &sku) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "machine_code/sku 必填");
    }

    int quantity = 0;
    int capacity = 50;
    int restock_threshold = 10;
    if (parse_int_field(body, "quantity", 1, 10000, &quantity) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity 必须为 1-10000 的整数");
    }

    json_t *v = json_object_get(body, "capacity");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n > 0) capacity = (int)n;
    }

    v = json_object_get(body, "restock_threshold");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) restock_threshold = (int)n;
    }

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char machine_code_copy[65];
    char sku_copy[65];
    char note_copy[257];
    snprintf(machine_code_copy, sizeof(machine_code_copy), "%s", machine_code);
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);
    snprintf(note_copy, sizeof(note_copy), "%s", note);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int machine_id = 0;
    const char *find_machine = "SELECT id FROM machines WHERE machine_code = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_machine, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询售货机失败");
    }
    sqlite3_bind_text(stmt, 1, machine_code_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "售货机不存在");
    }
    machine_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    int product_id = 0;
    const char *find_product = "SELECT id FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_product, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }
    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }
    product_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    int warehouse_stock = 0;
    const char *find_warehouse =
        "SELECT stock_quantity FROM products WHERE id = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_warehouse, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询总仓库存失败");
    }
    sqlite3_bind_int(stmt, 1, product_id);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        warehouse_stock = sqlite3_column_int(stmt, 0);
    }
    sqlite3_finalize(stmt);

    if (warehouse_stock < quantity) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "INSUFFICIENT_STOCK",
                            "总仓库存不足");
    }

    const char *upd_warehouse =
        "UPDATE products SET stock_quantity = stock_quantity - ?, "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_warehouse, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "扣减总仓库存失败");
    }
    sqlite3_bind_int(stmt, 1, quantity);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "扣减总仓库存失败");
    }

    const char *ins_movement =
        "INSERT INTO stock_movements "
        "(product_id, movement_type, quantity, unit_price_cents, note, "
        "operator_user_id) "
        "VALUES (?, 'OUT', ?, 0, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_movement, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入库存流水失败");
    }
    sqlite3_bind_int(stmt, 1, product_id);
    sqlite3_bind_int(stmt, 2, quantity);
    sqlite3_bind_text(stmt, 3, note_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 4, user.user_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "写入库存流水失败");
    }

    int current_stock = 0;
    int existing_id = 0;
    const char *find_stock =
        "SELECT id, stock_quantity FROM machine_stock "
        "WHERE machine_id = ? AND product_id = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_stock, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        existing_id = sqlite3_column_int(stmt, 0);
        current_stock = sqlite3_column_int(stmt, 1);
    }
    sqlite3_finalize(stmt);

    int new_stock = current_stock + quantity;
    if (new_stock > capacity) new_stock = capacity;
    int actual_added = new_stock - current_stock;

    if (existing_id > 0) {
        const char *upd_stock =
            "UPDATE machine_stock SET stock_quantity = ?, capacity = ?, "
            "restock_threshold = ?, last_restock_at = CURRENT_TIMESTAMP, "
            "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
        if (sqlite3_prepare_v2(g_db, upd_stock, -1, &stmt, NULL) != SQLITE_OK) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "更新库存失败");
        }
        sqlite3_bind_int(stmt, 1, new_stock);
        sqlite3_bind_int(stmt, 2, capacity);
        sqlite3_bind_int(stmt, 3, restock_threshold);
        sqlite3_bind_int(stmt, 4, existing_id);
    } else {
        const char *ins_stock =
            "INSERT INTO machine_stock (machine_id, product_id, stock_quantity, "
            "capacity, restock_threshold, last_restock_at) "
            "VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP);";
        if (sqlite3_prepare_v2(g_db, ins_stock, -1, &stmt, NULL) != SQLITE_OK) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "新增库存失败");
        }
        sqlite3_bind_int(stmt, 1, machine_id);
        sqlite3_bind_int(stmt, 2, product_id);
        sqlite3_bind_int(stmt, 3, new_stock);
        sqlite3_bind_int(stmt, 4, capacity);
        sqlite3_bind_int(stmt, 5, restock_threshold);
    }
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交补货事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "machine_code", json_string(machine_code_copy));
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "added_quantity", json_integer(actual_added));
    json_object_set_new(data, "stock_quantity", json_integer(new_stock));
    json_object_set_new(data, "capacity", json_integer(capacity));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_machine_stock_list(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *machine_code =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "machine_code");
    const char *low_stock =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "low_stock");

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT m.machine_code, m.location, p.sku, p.name, p.unit, "
        "ms.stock_quantity, ms.capacity, ms.restock_threshold, "
        "ms.last_restock_at, ms.updated_at "
        "FROM machine_stock ms "
        "JOIN machines m ON m.id = ms.machine_id "
        "JOIN products p ON p.id = ms.product_id ";

    char sql[2048];
    int use_machine = 0;
    int use_low = 0;
    const char *mc_val = NULL;

    if (machine_code != NULL && *machine_code != '\0') {
        use_machine = 1;
        mc_val = machine_code;
    }
    if (low_stock != NULL && *low_stock != '\0' && strcmp(low_stock, "1") == 0) {
        use_low = 1;
    }

    if (use_machine || use_low) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_machine) {
            strcat(sql, "m.machine_code = ? ");
            first = 0;
        }
        if (use_low) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "ms.stock_quantity <= ms.restock_threshold ");
        }
        strcat(sql, "ORDER BY ms.stock_quantity ASC, m.machine_code ASC;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY m.machine_code ASC, p.sku ASC;", sql_base);
    }

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询售货机库存失败");
    }

    int idx = 1;
    if (use_machine) {
        sqlite3_bind_text(stmt, idx++, mc_val, -1, SQLITE_TRANSIENT);
    }

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *item = json_object();
        json_object_set_new(item, "machine_code", json_string(safe_col_text(stmt, 0)));
        json_object_set_new(item, "location", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(item, "sku", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(item, "product_name", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(item, "unit", json_string(safe_col_text(stmt, 4)));
        json_object_set_new(item, "stock_quantity",
                            json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(item, "capacity",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(item, "restock_threshold",
                            json_integer(sqlite3_column_int(stmt, 7)));
        json_object_set_new(item, "last_restock_at",
                            json_string(safe_col_text(stmt, 8)));
        json_object_set_new(item, "updated_at", json_string(safe_col_text(stmt, 9)));
        json_array_append_new(items, item);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取售货机库存失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_machine_sale(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *machine_code = NULL;
    const char *sku = NULL;
    const char *payment_method = NULL;
    if (require_string_field(body, "machine_code", 64, &machine_code) != 0 ||
        require_string_field(body, "sku", 64, &sku) != 0 ||
        require_string_field(body, "payment_method", 16, &payment_method) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "machine_code/sku/payment_method 必填");
    }

    if (strcmp(payment_method, "cash") != 0 &&
        strcmp(payment_method, "scan") != 0 &&
        strcmp(payment_method, "other") != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "payment_method 仅支持 cash/scan/other");
    }

    int quantity = 0;
    int unit_price_cents = 0;
    if (parse_int_field(body, "quantity", 1, 1000, &quantity) != 0 ||
        parse_int_field(body, "unit_price_cents", 0, 1000000, &unit_price_cents) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "quantity/unit_price_cents 必须为合法整数");
    }

    int total_amount = quantity * unit_price_cents;

    const char *note = optional_string_field(body, "note", 256);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过256字符");
    }

    char machine_code_copy[65];
    char sku_copy[65];
    char payment_copy[17];
    char note_copy[257];
    snprintf(machine_code_copy, sizeof(machine_code_copy), "%s", machine_code);
    snprintf(sku_copy, sizeof(sku_copy), "%s", sku);
    snprintf(payment_copy, sizeof(payment_copy), "%s", payment_method);
    snprintf(note_copy, sizeof(note_copy), "%s", note);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    int has_auth = authenticate_request(connection, &user, token_hash);

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int machine_id = 0;
    const char *find_machine = "SELECT id, status FROM machines WHERE machine_code = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_machine, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询售货机失败");
    }
    sqlite3_bind_text(stmt, 1, machine_code_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "售货机不存在");
    }
    machine_id = sqlite3_column_int(stmt, 0);
    const char *m_status = safe_col_text(stmt, 1);
    sqlite3_finalize(stmt);

    if (strcmp(m_status, "online") != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "MACHINE_OFFLINE",
                            "售货机不在线，无法销售");
    }

    int product_id = 0;
    const char *find_product = "SELECT id FROM products WHERE sku = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_product, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询商品失败");
    }
    sqlite3_bind_text(stmt, 1, sku_copy, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "商品不存在");
    }
    product_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    int current_stock = 0;
    const char *find_stock =
        "SELECT stock_quantity FROM machine_stock "
        "WHERE machine_id = ? AND product_id = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_stock, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询库存失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    sqlite3_bind_int(stmt, 2, product_id);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        current_stock = sqlite3_column_int(stmt, 0);
    }
    sqlite3_finalize(stmt);

    if (current_stock < quantity) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "INSUFFICIENT_STOCK",
                            "售货机库存不足");
    }

    int new_stock = current_stock - quantity;
    const char *upd_stock =
        "UPDATE machine_stock SET stock_quantity = ?, "
        "updated_at = CURRENT_TIMESTAMP "
        "WHERE machine_id = ? AND product_id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_stock, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }
    sqlite3_bind_int(stmt, 1, new_stock);
    sqlite3_bind_int(stmt, 2, machine_id);
    sqlite3_bind_int(stmt, 3, product_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新库存失败");
    }

    const char *ins_sale =
        "INSERT INTO machine_sales (machine_id, product_id, quantity, "
        "unit_price_cents, total_amount_cents, payment_method, note, "
        "operator_user_id) VALUES (?, ?, ?, ?, ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_sale, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "记录销售失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    sqlite3_bind_int(stmt, 2, product_id);
    sqlite3_bind_int(stmt, 3, quantity);
    sqlite3_bind_int(stmt, 4, unit_price_cents);
    sqlite3_bind_int(stmt, 5, total_amount);
    sqlite3_bind_text(stmt, 6, payment_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 7, note_copy, -1, SQLITE_TRANSIENT);
    if (has_auth) {
        sqlite3_bind_int(stmt, 8, user.user_id);
    } else {
        sqlite3_bind_null(stmt, 8);
    }
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交销售事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "machine_code", json_string(machine_code_copy));
    json_object_set_new(data, "sku", json_string(sku_copy));
    json_object_set_new(data, "quantity", json_integer(quantity));
    json_object_set_new(data, "unit_price_cents", json_integer(unit_price_cents));
    json_object_set_new(data, "total_amount_cents", json_integer(total_amount));
    json_object_set_new(data, "payment_method", json_string(payment_copy));
    json_object_set_new(data, "stock_remaining", json_integer(new_stock));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_machine_sales_list(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *machine_code =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "machine_code");
    const char *payment_method =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "payment_method");
    const char *date =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "date");
    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT s.id, m.machine_code, m.location, p.sku, p.name, "
        "s.quantity, s.unit_price_cents, s.total_amount_cents, "
        "s.payment_method, s.note, u.username, s.created_at "
        "FROM machine_sales s "
        "JOIN machines m ON m.id = s.machine_id "
        "JOIN products p ON p.id = s.product_id "
        "LEFT JOIN users u ON u.id = s.operator_user_id ";

    char sql[2048];
    int use_machine = 0, use_payment = 0, use_date = 0;
    const char *mc_val = NULL, *pm_val = NULL, *date_val = NULL;

    if (machine_code != NULL && *machine_code != '\0') {
        use_machine = 1; mc_val = machine_code;
    }
    if (payment_method != NULL && *payment_method != '\0' &&
        (strcmp(payment_method, "cash") == 0 ||
         strcmp(payment_method, "scan") == 0 ||
         strcmp(payment_method, "other") == 0)) {
        use_payment = 1; pm_val = payment_method;
    }
    if (date != NULL && *date != '\0' && strlen(date) == 10) {
        use_date = 1; date_val = date;
    }

    if (use_machine || use_payment || use_date) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_machine) {
            strcat(sql, "m.machine_code = ? ");
            first = 0;
        }
        if (use_payment) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "s.payment_method = ? ");
            first = 0;
        }
        if (use_date) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "DATE(s.created_at) = ? ");
        }
        strcat(sql, "ORDER BY s.id DESC LIMIT ?;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY s.id DESC LIMIT ?;", sql_base);
    }

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询销售记录失败");
    }

    int idx = 1;
    if (use_machine) sqlite3_bind_text(stmt, idx++, mc_val, -1, SQLITE_TRANSIENT);
    if (use_payment) sqlite3_bind_text(stmt, idx++, pm_val, -1, SQLITE_TRANSIENT);
    if (use_date) sqlite3_bind_text(stmt, idx++, date_val, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "machine_code", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "location", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "sku", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "product_name", json_string(safe_col_text(stmt, 4)));
        json_object_set_new(it, "quantity", json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(it, "unit_price_cents",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(it, "total_amount_cents",
                            json_integer(sqlite3_column_int(stmt, 7)));
        json_object_set_new(it, "payment_method", json_string(safe_col_text(stmt, 8)));
        json_object_set_new(it, "note", json_string(safe_col_text(stmt, 9)));
        json_object_set_new(it, "operator", json_string(safe_col_text(stmt, 10)));
        json_object_set_new(it, "created_at", json_string(safe_col_text(stmt, 11)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取销售记录失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_downtime_start(struct MHD_Connection *connection,
                                              ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *machine_code = NULL;
    const char *reason = NULL;
    if (require_string_field(body, "machine_code", 64, &machine_code) != 0 ||
        require_string_field(body, "reason", 512, &reason) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "machine_code/reason 必填");
    }

    int estimated_loss_cents = 0;
    json_t *v = json_object_get(body, "estimated_loss_cents");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) estimated_loss_cents = (int)n;
    }

    const char *note = optional_string_field(body, "note", 512);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串且不超过512字符");
    }

    char machine_code_copy[65];
    char reason_copy[513];
    char note_copy[513];
    snprintf(machine_code_copy, sizeof(machine_code_copy), "%s", machine_code);
    snprintf(reason_copy, sizeof(reason_copy), "%s", reason);
    snprintf(note_copy, sizeof(note_copy), "%s", note);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    int has_auth = authenticate_request(connection, &user, token_hash);

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int machine_id = 0;
    int hourly_sales = 0;
    const char *find_machine =
        "SELECT id, estimated_hourly_sales_cents FROM machines "
        "WHERE machine_code = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_machine, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询售货机失败");
    }
    sqlite3_bind_text(stmt, 1, machine_code_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "售货机不存在");
    }
    machine_id = sqlite3_column_int(stmt, 0);
    hourly_sales = sqlite3_column_int(stmt, 1);
    sqlite3_finalize(stmt);

    int unresolved = 0;
    const char *check_sql =
        "SELECT COUNT(*) FROM machine_downtime "
        "WHERE machine_id = ? AND resolved = 0;";
    if (sqlite3_prepare_v2(g_db, check_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "检查未解决停机失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        unresolved = sqlite3_column_int(stmt, 0);
    }
    sqlite3_finalize(stmt);

    if (unresolved > 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "DOWNTIME_EXISTS",
                            "该机存在未解决的停机记录");
    }

    if (estimated_loss_cents == 0 && hourly_sales > 0) {
        estimated_loss_cents = hourly_sales / 60;
    }

    const char *ins_downtime =
        "INSERT INTO machine_downtime (machine_id, start_time, reason, "
        "estimated_loss_cents, operator_user_id, note) "
        "VALUES (?, CURRENT_TIMESTAMP, ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_downtime, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "记录停机失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    sqlite3_bind_text(stmt, 2, reason_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 3, estimated_loss_cents);
    if (has_auth) {
        sqlite3_bind_int(stmt, 4, user.user_id);
    } else {
        sqlite3_bind_null(stmt, 4);
    }
    sqlite3_bind_text(stmt, 5, note_copy, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    const char *upd_status =
        "UPDATE machines SET status = 'downtime', "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_status, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新售货机状态失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交停机事务失败");
    }

    int downtime_id = (int)sqlite3_last_insert_rowid(g_db);
    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "downtime_id", json_integer(downtime_id));
    json_object_set_new(data, "machine_code", json_string(machine_code_copy));
    json_object_set_new(data, "reason", json_string(reason_copy));
    json_object_set_new(data, "estimated_loss_per_minute_cents",
                        json_integer(estimated_loss_cents));
    json_object_set_new(data, "status", json_string("started"));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_downtime_end(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    int downtime_id = 0;
    if (parse_int_field(body, "downtime_id", 1, 1000000, &downtime_id) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "downtime_id 必填且为正整数");
    }

    int actual_loss_cents = -1;
    json_t *v = json_object_get(body, "actual_loss_cents");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) actual_loss_cents = (int)n;
    }

    const char *resolution_note = optional_string_field(body, "resolution_note", 512);
    if (resolution_note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "resolution_note 需为字符串");
    }

    char resolution_copy[513];
    snprintf(resolution_copy, sizeof(resolution_copy), "%s",
             resolution_note != NULL ? resolution_note : "");

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    int has_auth = authenticate_request(connection, &user, token_hash);

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int machine_id = 0;
    int estimated_per_min = 0;
    char start_time[64] = {0};
    const char *find_dt =
        "SELECT machine_id, start_time, estimated_loss_cents, resolved "
        "FROM machine_downtime WHERE id = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_dt, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询停机记录失败");
    }
    sqlite3_bind_int(stmt, 1, downtime_id);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "停机记录不存在");
    }
    machine_id = sqlite3_column_int(stmt, 0);
    snprintf(start_time, sizeof(start_time), "%s", safe_col_text(stmt, 1));
    estimated_per_min = sqlite3_column_int(stmt, 2);
    int resolved = sqlite3_column_int(stmt, 3);
    sqlite3_finalize(stmt);

    if (resolved) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "ALREADY_RESOLVED",
                            "该停机记录已解决");
    }

    int duration_min = 0;
    int total_loss = 0;

    const char *calc_sql =
        "SELECT "
        "CAST((julianday(CURRENT_TIMESTAMP) - julianday(?)) * 24 * 60 AS INTEGER);";
    if (sqlite3_prepare_v2(g_db, calc_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "计算停机时长失败");
    }
    sqlite3_bind_text(stmt, 1, start_time, -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) {
        duration_min = sqlite3_column_int(stmt, 0);
        if (duration_min < 1) duration_min = 1;
    }
    sqlite3_finalize(stmt);

    if (actual_loss_cents >= 0) {
        total_loss = actual_loss_cents;
    } else {
        total_loss = estimated_per_min * duration_min;
    }

    const char *upd_dt =
        "UPDATE machine_downtime SET end_time = CURRENT_TIMESTAMP, "
        "duration_minutes = ?, estimated_loss_cents = ?, resolved = 1, "
        "resolution_note = ?, operator_user_id = ? WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_dt, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新停机记录失败");
    }
    sqlite3_bind_int(stmt, 1, duration_min);
    sqlite3_bind_int(stmt, 2, total_loss);
    sqlite3_bind_text(stmt, 3, resolution_copy, -1, SQLITE_TRANSIENT);
    if (has_auth) {
        sqlite3_bind_int(stmt, 4, user.user_id);
    } else {
        sqlite3_bind_null(stmt, 4);
    }
    sqlite3_bind_int(stmt, 5, downtime_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    const char *upd_machine =
        "UPDATE machines SET status = 'online', "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_machine, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新售货机状态失败");
    }
    sqlite3_bind_int(stmt, 1, machine_id);
    sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交解决停机事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "downtime_id", json_integer(downtime_id));
    json_object_set_new(data, "duration_minutes", json_integer(duration_min));
    json_object_set_new(data, "total_loss_cents", json_integer(total_loss));
    json_object_set_new(data, "status", json_string("resolved"));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_downtime_list(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *machine_code =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "machine_code");
    const char *resolved =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "resolved");
    const char *date =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "date");
    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT d.id, m.machine_code, m.location, d.start_time, d.end_time, "
        "d.duration_minutes, d.reason, d.estimated_loss_cents, d.resolved, "
        "d.resolution_note, u.username, d.created_at "
        "FROM machine_downtime d "
        "JOIN machines m ON m.id = d.machine_id "
        "LEFT JOIN users u ON u.id = d.operator_user_id ";

    char sql[2048];
    int use_machine = 0, use_resolved = 0, use_date = 0;
    const char *mc_val = NULL, *date_val = NULL;
    int resolved_val = -1;

    if (machine_code != NULL && *machine_code != '\0') {
        use_machine = 1; mc_val = machine_code;
    }
    if (resolved != NULL && *resolved != '\0') {
        if (strcmp(resolved, "0") == 0 || strcmp(resolved, "1") == 0) {
            use_resolved = 1;
            resolved_val = strcmp(resolved, "1") == 0 ? 1 : 0;
        }
    }
    if (date != NULL && *date != '\0' && strlen(date) == 10) {
        use_date = 1; date_val = date;
    }

    if (use_machine || use_resolved || use_date) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_machine) {
            strcat(sql, "m.machine_code = ? ");
            first = 0;
        }
        if (use_resolved) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "d.resolved = ? ");
            first = 0;
        }
        if (use_date) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "DATE(d.start_time) = ? ");
        }
        strcat(sql, "ORDER BY d.id DESC LIMIT ?;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY d.id DESC LIMIT ?;", sql_base);
    }

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询停机记录失败");
    }

    int idx = 1;
    if (use_machine) sqlite3_bind_text(stmt, idx++, mc_val, -1, SQLITE_TRANSIENT);
    if (use_resolved) sqlite3_bind_int(stmt, idx++, resolved_val);
    if (use_date) sqlite3_bind_text(stmt, idx++, date_val, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "machine_code", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "location", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "start_time", json_string(safe_col_text(stmt, 3)));
        json_object_set_new(it, "end_time", json_string(safe_col_text(stmt, 4)));
        json_object_set_new(it, "duration_minutes",
                            json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(it, "reason", json_string(safe_col_text(stmt, 6)));
        json_object_set_new(it, "loss_cents",
                            json_integer(sqlite3_column_int(stmt, 7)));
        json_object_set_new(it, "resolved",
                            json_integer(sqlite3_column_int(stmt, 8)));
        json_object_set_new(it, "resolution_note", json_string(safe_col_text(stmt, 9)));
        json_object_set_new(it, "operator", json_string(safe_col_text(stmt, 10)));
        json_object_set_new(it, "created_at", json_string(safe_col_text(stmt, 11)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取停机记录失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_replenishment_generate(struct MHD_Connection *connection,
                                                     ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    int has_body = (parse_json_body(ci, &body, err) == 0);

    const char *route_date = NULL;
    int min_priority = 0;
    int max_machines = 0;

    if (has_body && body != NULL) {
        route_date = optional_string_field(body, "route_date", 10);
        json_t *v = json_object_get(body, "min_priority");
        if (json_is_integer(v)) {
            json_int_t n = json_integer_value(v);
            if (n >= 0 && n <= 100) min_priority = (int)n;
        }
        v = json_object_get(body, "max_machines");
        if (json_is_integer(v)) {
            json_int_t n = json_integer_value(v);
            if (n > 0) max_machines = (int)n;
        }
    }

    char date_buf[16] = {0};
    if (route_date == NULL || *route_date == '\0') {
        time_t t = now_epoch();
        struct tm *tm_info = localtime(&t);
        strftime(date_buf, sizeof(date_buf), "%Y-%m-%d", tm_info);
        route_date = date_buf;
    }

    char route_date_copy[16];
    snprintf(route_date_copy, sizeof(route_date_copy), "%s", route_date);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int existing_route = 0;
    const char *check_sql =
        "SELECT id FROM replenishment_routes WHERE route_date = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, check_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "检查已有路线失败");
    }
    sqlite3_bind_text(stmt, 1, route_date_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) existing_route = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    if (existing_route > 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        json_t *data = json_object();
        json_object_set_new(data, "route_id", json_integer(existing_route));
        json_object_set_new(data, "route_date", json_string(route_date_copy));
        json_object_set_new(data, "message", json_string("当日路线已存在"));
        return respond_success(connection, MHD_HTTP_OK, data);
    }

    const char *machines_sql =
        "SELECT m.id, m.machine_code, m.location, m.status, m.door_error, "
        "m.temp_alert, m.priority_weight, m.estimated_hourly_sales_cents, "
        "COALESCE(SUM(CASE WHEN ms.stock_quantity <= ms.restock_threshold THEN 1 ELSE 0 END), 0) as low_stock_count, "
        "COALESCE(SUM(CASE WHEN ms.stock_quantity <= ms.restock_threshold "
        "THEN (ms.capacity - ms.stock_quantity) ELSE 0 END), 0) as products_needed, "
        "COALESCE(SUM(ms.stock_quantity), 0) as total_stock, "
        "COALESCE(SUM(ms.capacity), 0) as total_capacity, "
        "COALESCE((SELECT SUM(total_amount_cents) FROM machine_sales s "
        "WHERE s.machine_id = m.id AND DATE(s.created_at) = DATE('now','-1 day')), 0) as yesterday_sales "
        "FROM machines m "
        "LEFT JOIN machine_stock ms ON ms.machine_id = m.id "
        "WHERE m.status != 'downtime' "
        "GROUP BY m.id "
        "HAVING m.priority_weight >= ? "
        "ORDER BY "
        "(CASE WHEN m.door_error = 1 OR m.temp_alert = 1 THEN 1 ELSE 0 END) DESC, "
        "(CASE WHEN COALESCE(SUM(CASE WHEN ms.stock_quantity <= ms.restock_threshold THEN 1 ELSE 0 END), 0) > 0 THEN 1 ELSE 0 END) DESC, "
        "(COALESCE(SUM(ms.capacity), 0) - COALESCE(SUM(ms.stock_quantity), 0)) DESC, "
        "yesterday_sales DESC, "
        "m.priority_weight DESC;";

    if (sqlite3_prepare_v2(g_db, machines_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询补货机器失败");
    }
    sqlite3_bind_int(stmt, 1, min_priority);

    json_t *machines = json_array();
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        int m_id = sqlite3_column_int(stmt, 0);
        const char *m_code = safe_col_text(stmt, 1);
        const char *m_loc = safe_col_text(stmt, 2);
        const char *m_status = safe_col_text(stmt, 3);
        int door_err = sqlite3_column_int(stmt, 4);
        int temp_al = sqlite3_column_int(stmt, 5);
        int p_weight = sqlite3_column_int(stmt, 6);
        int low_stock = sqlite3_column_int(stmt, 8);
        int products_needed = sqlite3_column_int(stmt, 9);
        int total_stock = sqlite3_column_int(stmt, 10);
        int total_capacity = sqlite3_column_int(stmt, 11);
        int yest_sales = sqlite3_column_int(stmt, 12);

        int stock_ratio = total_capacity > 0 ?
            (int)((double)(total_capacity - total_stock) / total_capacity * 100) : 0;
        int priority_score = p_weight;
        if (door_err) priority_score += 30;
        if (temp_al) priority_score += 25;
        if (low_stock > 0) priority_score += 20;
        priority_score += stock_ratio / 4;
        if (yest_sales > 5000) priority_score += 15;

        char reason[256] = {0};
        int rlen = 0;
        if (low_stock > 0) {
            rlen += snprintf(reason + rlen, sizeof(reason) - rlen,
                             "库存不足(%d种商品); ", low_stock);
        }
        if (door_err) {
            rlen += snprintf(reason + rlen, sizeof(reason) - rlen, "柜门异常; ");
        }
        if (temp_al) {
            rlen += snprintf(reason + rlen, sizeof(reason) - rlen, "温度告警; ");
        }

        json_t *m = json_object();
        json_object_set_new(m, "machine_id", json_integer(m_id));
        json_object_set_new(m, "machine_code", json_string(m_code));
        json_object_set_new(m, "location", json_string(m_loc));
        json_object_set_new(m, "status", json_string(m_status));
        json_object_set_new(m, "door_error", json_integer(door_err));
        json_object_set_new(m, "temp_alert", json_integer(temp_al));
        json_object_set_new(m, "priority_weight", json_integer(p_weight));
        json_object_set_new(m, "priority_score", json_integer(priority_score));
        json_object_set_new(m, "low_stock_count", json_integer(low_stock));
        json_object_set_new(m, "products_needed", json_integer(products_needed));
        json_object_set_new(m, "stock_available", json_integer(total_stock));
        json_object_set_new(m, "capacity", json_integer(total_capacity));
        json_object_set_new(m, "yesterday_sales_cents", json_integer(yest_sales));
        json_object_set_new(m, "reason", json_string(reason));
        json_array_append_new(machines, m);
    }
    sqlite3_finalize(stmt);

    if (max_machines > 0 && (int)json_array_size(machines) > max_machines) {
        for (int i = max_machines; i < (int)json_array_size(machines); i++) {
            json_array_remove(machines, i);
        }
    }

    int total_machines = (int)json_array_size(machines);
    if (total_machines == 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        json_t *data = json_object();
        json_object_set_new(data, "route_date", json_string(route_date_copy));
        json_object_set_new(data, "total_machines", json_integer(0));
        json_object_set_new(data, "message", json_string("没有需要补货的机器"));
        return respond_success(connection, MHD_HTTP_OK, data);
    }

    const char *ins_route =
        "INSERT INTO replenishment_routes (route_date, operator_user_id, "
        "total_machines, note) VALUES (?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_route, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(machines);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建补货路线失败");
    }
    sqlite3_bind_text(stmt, 1, route_date_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 2, user.user_id);
    sqlite3_bind_int(stmt, 3, total_machines);
    sqlite3_bind_text(stmt, 4, "自动生成路线", -1, SQLITE_TRANSIENT);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);
    if (rc != SQLITE_DONE) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(machines);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建补货路线失败");
    }

    int route_id = (int)sqlite3_last_insert_rowid(g_db);

    const char *ins_item =
        "INSERT INTO replenishment_route_items (route_id, machine_id, "
        "priority_score, sort_order, low_stock_reason, door_error, "
        "temp_alert, estimated_products_needed) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_item, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(machines);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建路线项失败");
    }

    for (size_t i = 0; i < json_array_size(machines); i++) {
        json_t *m = json_array_get(machines, i);
        int m_id = json_integer_value(json_object_get(m, "machine_id"));
        int score = json_integer_value(json_object_get(m, "priority_score"));
        int products = json_integer_value(json_object_get(m, "products_needed"));
        int door_err = json_integer_value(json_object_get(m, "door_error"));
        int temp_al = json_integer_value(json_object_get(m, "temp_alert"));
        const char *reason = json_string_value(json_object_get(m, "reason"));

        sqlite3_bind_int(stmt, 1, route_id);
        sqlite3_bind_int(stmt, 2, m_id);
        sqlite3_bind_int(stmt, 3, score);
        sqlite3_bind_int(stmt, 4, (int)i + 1);
        sqlite3_bind_text(stmt, 5, reason, -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 6, door_err);
        sqlite3_bind_int(stmt, 7, temp_al);
        sqlite3_bind_int(stmt, 8, products);
        sqlite3_step(stmt);
        sqlite3_reset(stmt);
    }
    sqlite3_finalize(stmt);

    if (commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(machines);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交补货路线事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    if (has_body && body != NULL) json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "route_id", json_integer(route_id));
    json_object_set_new(data, "route_date", json_string(route_date_copy));
    json_object_set_new(data, "total_machines", json_integer(total_machines));
    json_object_set_new(data, "machines", machines);
    return respond_success(connection, MHD_HTTP_CREATED, data);
}

static enum MHD_Result handle_replenishment_list(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *date =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "date");
    const char *status =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "status");
    const char *with_items =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "with_items");
    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT r.id, r.route_date, r.status, r.total_machines, "
        "r.completed_machines, r.note, u.username, r.created_at "
        "FROM replenishment_routes r "
        "LEFT JOIN users u ON u.id = r.operator_user_id ";

    char sql[2048];
    int use_date = 0, use_status = 0;
    const char *date_val = NULL, *status_val = NULL;

    if (date != NULL && *date != '\0' && strlen(date) == 10) {
        use_date = 1; date_val = date;
    }
    if (status != NULL && *status != '\0' &&
        (strcmp(status, "pending") == 0 || strcmp(status, "in_progress") == 0 ||
         strcmp(status, "completed") == 0 || strcmp(status, "cancelled") == 0)) {
        use_status = 1; status_val = status;
    }

    if (use_date || use_status) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_date) {
            strcat(sql, "r.route_date = ? ");
            first = 0;
        }
        if (use_status) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "r.status = ? ");
        }
        strcat(sql, "ORDER BY r.id DESC LIMIT ?;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY r.id DESC LIMIT ?;", sql_base);
    }

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询补货路线失败");
    }

    int idx = 1;
    if (use_date) sqlite3_bind_text(stmt, idx++, date_val, -1, SQLITE_TRANSIENT);
    if (use_status) sqlite3_bind_text(stmt, idx++, status_val, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        int route_id = sqlite3_column_int(stmt, 0);
        json_object_set_new(it, "id", json_integer(route_id));
        json_object_set_new(it, "route_date", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "status", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "total_machines",
                            json_integer(sqlite3_column_int(stmt, 3)));
        json_object_set_new(it, "completed_machines",
                            json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(it, "note", json_string(safe_col_text(stmt, 5)));
        json_object_set_new(it, "operator", json_string(safe_col_text(stmt, 6)));
        json_object_set_new(it, "created_at", json_string(safe_col_text(stmt, 7)));

        if (with_items != NULL && strcmp(with_items, "1") == 0) {
            sqlite3_stmt *stmt2 = NULL;
            const char *items_sql =
                "SELECT ri.id, ri.sort_order, ri.priority_score, ri.status, "
                "ri.low_stock_reason, ri.door_error, ri.temp_alert, "
                "ri.estimated_products_needed, ri.actual_products_restocked, "
                "ri.note, ri.completed_at, m.machine_code, m.location "
                "FROM replenishment_route_items ri "
                "JOIN machines m ON m.id = ri.machine_id "
                "WHERE ri.route_id = ? ORDER BY ri.sort_order ASC;";
            if (sqlite3_prepare_v2(g_db, items_sql, -1, &stmt2, NULL) == SQLITE_OK) {
                sqlite3_bind_int(stmt2, 1, route_id);
                json_t *route_items = json_array();
                while (sqlite3_step(stmt2) == SQLITE_ROW) {
                    json_t *ri = json_object();
                    json_object_set_new(ri, "id",
                                        json_integer(sqlite3_column_int(stmt2, 0)));
                    json_object_set_new(ri, "sort_order",
                                        json_integer(sqlite3_column_int(stmt2, 1)));
                    json_object_set_new(ri, "priority_score",
                                        json_integer(sqlite3_column_int(stmt2, 2)));
                    json_object_set_new(ri, "status",
                                        json_string(safe_col_text(stmt2, 3)));
                    json_object_set_new(ri, "low_stock_reason",
                                        json_string(safe_col_text(stmt2, 4)));
                    json_object_set_new(ri, "door_error",
                                        json_integer(sqlite3_column_int(stmt2, 5)));
                    json_object_set_new(ri, "temp_alert",
                                        json_integer(sqlite3_column_int(stmt2, 6)));
                    json_object_set_new(ri, "estimated_products_needed",
                                        json_integer(sqlite3_column_int(stmt2, 7)));
                    json_object_set_new(ri, "actual_products_restocked",
                                        json_integer(sqlite3_column_int(stmt2, 8)));
                    json_object_set_new(ri, "note",
                                        json_string(safe_col_text(stmt2, 9)));
                    json_object_set_new(ri, "completed_at",
                                        json_string(safe_col_text(stmt2, 10)));
                    json_object_set_new(ri, "machine_code",
                                        json_string(safe_col_text(stmt2, 11)));
                    json_object_set_new(ri, "location",
                                        json_string(safe_col_text(stmt2, 12)));
                    json_array_append_new(route_items, ri);
                }
                sqlite3_finalize(stmt2);
                json_object_set_new(it, "items", route_items);
            }
        }
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取补货路线失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_replenishment_complete_item(struct MHD_Connection *connection,
                                                           ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    int item_id = 0;
    if (parse_int_field(body, "item_id", 1, 1000000, &item_id) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "item_id 必填且为正整数");
    }

    int actual_restocked = 0;
    json_t *v = json_object_get(body, "actual_products_restocked");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) actual_restocked = (int)n;
    }

    const char *status = optional_string_field(body, "status", 16);
    if (status == NULL || *status == '\0') { status = "completed"; }
    if (strcmp(status, "completed") != 0 && strcmp(status, "skipped") != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "status 仅支持 completed/skipped");
    }

    const char *note = optional_string_field(body, "note", 512);
    if (note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "note 需为字符串");
    }

    char status_copy[17];
    char note_copy[513];
    snprintf(status_copy, sizeof(status_copy), "%s", status);
    snprintf(note_copy, sizeof(note_copy), "%s", note != NULL ? note : "");

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int route_id = 0;
    const char *find_sql = "SELECT route_id FROM replenishment_route_items WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询路线项失败");
    }
    sqlite3_bind_int(stmt, 1, item_id);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "路线项不存在");
    }
    route_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    const char *upd_item =
        "UPDATE replenishment_route_items SET status = ?, "
        "actual_products_restocked = ?, note = ?, "
        "completed_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_item, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新路线项失败");
    }
    sqlite3_bind_text(stmt, 1, status_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 2, actual_restocked);
    sqlite3_bind_text(stmt, 3, note_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 4, item_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    int completed = 0;
    int total = 0;
    const char *count_sql =
        "SELECT COALESCE(SUM(CASE WHEN status = 'completed' THEN 1 ELSE 0 END), 0), "
        "COUNT(*) FROM replenishment_route_items WHERE route_id = ?;";
    if (sqlite3_prepare_v2(g_db, count_sql, -1, &stmt, NULL) == SQLITE_OK) {
        sqlite3_bind_int(stmt, 1, route_id);
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            completed = sqlite3_column_int(stmt, 0);
            total = sqlite3_column_int(stmt, 1);
        }
        sqlite3_finalize(stmt);
    }

    const char *route_status = (completed >= total && total > 0) ? "completed" : "in_progress";
    const char *upd_route =
        "UPDATE replenishment_routes SET status = ?, completed_machines = ?, "
        "updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_route, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新路线状态失败");
    }
    sqlite3_bind_text(stmt, 1, route_status, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 2, completed);
    sqlite3_bind_int(stmt, 3, route_id);
    sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "item_id", json_integer(item_id));
    json_object_set_new(data, "status", json_string(status_copy));
    json_object_set_new(data, "actual_products_restocked", json_integer(actual_restocked));
    json_object_set_new(data, "route_status", json_string(route_status));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_daily_report_generate(struct MHD_Connection *connection,
                                                     ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    int has_body = (parse_json_body(ci, &body, err) == 0);

    const char *report_date = NULL;
    if (has_body && body != NULL) {
        report_date = optional_string_field(body, "report_date", 10);
    }

    char date_buf[16] = {0};
    if (report_date == NULL || *report_date == '\0') {
        time_t t = now_epoch();
        struct tm *tm_info = localtime(&t);
        strftime(date_buf, sizeof(date_buf), "%Y-%m-%d", tm_info);
        report_date = date_buf;
    }

    char report_date_copy[16];
    snprintf(report_date_copy, sizeof(report_date_copy), "%s", report_date);

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (begin_transaction() != 0) {
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "开启事务失败");
    }

    sqlite3_stmt *stmt = NULL;
    int existing_id = 0;
    const char *check_sql =
        "SELECT id FROM daily_reports WHERE report_date = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, check_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "检查已有日报失败");
    }
    sqlite3_bind_text(stmt, 1, report_date_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc == SQLITE_ROW) existing_id = sqlite3_column_int(stmt, 0);
    sqlite3_finalize(stmt);

    int total_sales = 0, cash_sales = 0, scan_sales = 0, other_sales = 0;
    int total_trans = 0, total_qty = 0;
    const char *sales_sql =
        "SELECT COALESCE(SUM(total_amount_cents), 0), "
        "COALESCE(SUM(CASE WHEN payment_method='cash' THEN total_amount_cents ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN payment_method='scan' THEN total_amount_cents ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN payment_method='other' THEN total_amount_cents ELSE 0 END), 0), "
        "COUNT(*), COALESCE(SUM(quantity), 0) "
        "FROM machine_sales WHERE DATE(created_at) = ?;";
    if (sqlite3_prepare_v2(g_db, sales_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "统计销售数据失败");
    }
    sqlite3_bind_text(stmt, 1, report_date_copy, -1, SQLITE_TRANSIENT);
    if (sqlite3_step(stmt) == SQLITE_ROW) {
        total_sales = sqlite3_column_int(stmt, 0);
        cash_sales = sqlite3_column_int(stmt, 1);
        scan_sales = sqlite3_column_int(stmt, 2);
        other_sales = sqlite3_column_int(stmt, 3);
        total_trans = sqlite3_column_int(stmt, 4);
        total_qty = sqlite3_column_int(stmt, 5);
    }
    sqlite3_finalize(stmt);

    int downtime_loss = 0, downtime_min = 0;
    const char *dt_sql =
        "SELECT COALESCE(SUM(CASE WHEN duration_minutes IS NOT NULL "
        "THEN estimated_loss_cents ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN duration_minutes IS NOT NULL "
        "THEN duration_minutes ELSE 0 END), 0) "
        "FROM machine_downtime WHERE DATE(start_time) = ? AND resolved = 1;";
    if (sqlite3_prepare_v2(g_db, dt_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "统计停机损失失败");
    }
    sqlite3_bind_text(stmt, 1, report_date_copy, -1, SQLITE_TRANSIENT);
    if (sqlite3_step(stmt) == SQLITE_ROW) {
        downtime_loss = sqlite3_column_int(stmt, 0);
        downtime_min = sqlite3_column_int(stmt, 1);
    }
    sqlite3_finalize(stmt);

    int online = 0, offline = 0, downtime_cnt = 0, door_err = 0, temp_al = 0;
    const char *mach_sql =
        "SELECT "
        "COALESCE(SUM(CASE WHEN status='online' THEN 1 ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN status='offline' THEN 1 ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN status='downtime' THEN 1 ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN door_error=1 THEN 1 ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN temp_alert=1 THEN 1 ELSE 0 END), 0) "
        "FROM machines;";
    if (sqlite3_prepare_v2(g_db, mach_sql, -1, &stmt, NULL) != SQLITE_OK) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "统计机器状态失败");
    }
    if (sqlite3_step(stmt) == SQLITE_ROW) {
        online = sqlite3_column_int(stmt, 0);
        offline = sqlite3_column_int(stmt, 1);
        downtime_cnt = sqlite3_column_int(stmt, 2);
        door_err = sqlite3_column_int(stmt, 3);
        temp_al = sqlite3_column_int(stmt, 4);
    }
    sqlite3_finalize(stmt);

    if (existing_id > 0) {
        const char *upd_sql =
            "UPDATE daily_reports SET total_sales_cents = ?, cash_sales_cents = ?, "
            "scan_sales_cents = ?, other_sales_cents = ?, total_transactions = ?, "
            "total_quantity_sold = ?, total_downtime_loss_cents = ?, "
            "total_downtime_minutes = ?, expected_cash_cents = ?, "
            "expected_scan_cents = ?, machines_online = ?, machines_offline = ?, "
            "machines_in_downtime = ?, machines_with_door_errors = ?, "
            "machines_with_temp_alerts = ?, updated_at = CURRENT_TIMESTAMP "
            "WHERE id = ?;";
        if (sqlite3_prepare_v2(g_db, upd_sql, -1, &stmt, NULL) != SQLITE_OK) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            if (has_body && body != NULL) json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "更新日报失败");
        }
        sqlite3_bind_int(stmt, 1, total_sales);
        sqlite3_bind_int(stmt, 2, cash_sales);
        sqlite3_bind_int(stmt, 3, scan_sales);
        sqlite3_bind_int(stmt, 4, other_sales);
        sqlite3_bind_int(stmt, 5, total_trans);
        sqlite3_bind_int(stmt, 6, total_qty);
        sqlite3_bind_int(stmt, 7, downtime_loss);
        sqlite3_bind_int(stmt, 8, downtime_min);
        sqlite3_bind_int(stmt, 9, cash_sales);
        sqlite3_bind_int(stmt, 10, scan_sales);
        sqlite3_bind_int(stmt, 11, online);
        sqlite3_bind_int(stmt, 12, offline);
        sqlite3_bind_int(stmt, 13, downtime_cnt);
        sqlite3_bind_int(stmt, 14, door_err);
        sqlite3_bind_int(stmt, 15, temp_al);
        sqlite3_bind_int(stmt, 16, existing_id);
        rc = sqlite3_step(stmt);
        sqlite3_finalize(stmt);
    } else {
        const char *ins_sql =
            "INSERT INTO daily_reports (report_date, total_sales_cents, "
            "cash_sales_cents, scan_sales_cents, other_sales_cents, "
            "total_transactions, total_quantity_sold, total_downtime_loss_cents, "
            "total_downtime_minutes, expected_cash_cents, expected_scan_cents, "
            "machines_online, machines_offline, machines_in_downtime, "
            "machines_with_door_errors, machines_with_temp_alerts, operator_user_id) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);";
        if (sqlite3_prepare_v2(g_db, ins_sql, -1, &stmt, NULL) != SQLITE_OK) {
            rollback_transaction();
            pthread_mutex_unlock(&g_db_mutex);
            if (has_body && body != NULL) json_decref(body);
            return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                                "DB_ERROR", "创建日报失败");
        }
        sqlite3_bind_text(stmt, 1, report_date_copy, -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 2, total_sales);
        sqlite3_bind_int(stmt, 3, cash_sales);
        sqlite3_bind_int(stmt, 4, scan_sales);
        sqlite3_bind_int(stmt, 5, other_sales);
        sqlite3_bind_int(stmt, 6, total_trans);
        sqlite3_bind_int(stmt, 7, total_qty);
        sqlite3_bind_int(stmt, 8, downtime_loss);
        sqlite3_bind_int(stmt, 9, downtime_min);
        sqlite3_bind_int(stmt, 10, cash_sales);
        sqlite3_bind_int(stmt, 11, scan_sales);
        sqlite3_bind_int(stmt, 12, online);
        sqlite3_bind_int(stmt, 13, offline);
        sqlite3_bind_int(stmt, 14, downtime_cnt);
        sqlite3_bind_int(stmt, 15, door_err);
        sqlite3_bind_int(stmt, 16, temp_al);
        sqlite3_bind_int(stmt, 17, user.user_id);
        rc = sqlite3_step(stmt);
        sqlite3_finalize(stmt);
        existing_id = (int)sqlite3_last_insert_rowid(g_db);
    }

    if (rc != SQLITE_DONE || commit_transaction() != 0) {
        rollback_transaction();
        pthread_mutex_unlock(&g_db_mutex);
        if (has_body && body != NULL) json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "提交日报事务失败");
    }

    pthread_mutex_unlock(&g_db_mutex);
    if (has_body && body != NULL) json_decref(body);

    json_t *data = json_object();
    json_object_set_new(data, "report_id", json_integer(existing_id));
    json_object_set_new(data, "report_date", json_string(report_date_copy));
    json_object_set_new(data, "total_sales_cents", json_integer(total_sales));
    json_object_set_new(data, "cash_sales_cents", json_integer(cash_sales));
    json_object_set_new(data, "scan_sales_cents", json_integer(scan_sales));
    json_object_set_new(data, "other_sales_cents", json_integer(other_sales));
    json_object_set_new(data, "total_transactions", json_integer(total_trans));
    json_object_set_new(data, "total_quantity_sold", json_integer(total_qty));
    json_object_set_new(data, "total_downtime_loss_cents", json_integer(downtime_loss));
    json_object_set_new(data, "total_downtime_minutes", json_integer(downtime_min));
    json_object_set_new(data, "machines_online", json_integer(online));
    json_object_set_new(data, "machines_offline", json_integer(offline));
    json_object_set_new(data, "machines_in_downtime", json_integer(downtime_cnt));
    json_object_set_new(data, "machines_with_door_errors", json_integer(door_err));
    json_object_set_new(data, "machines_with_temp_alerts", json_integer(temp_al));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_daily_report_list(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *date =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "date");
    const char *reconciled =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "reconciled");
    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT r.id, r.report_date, r.total_sales_cents, r.cash_sales_cents, "
        "r.scan_sales_cents, r.other_sales_cents, r.total_transactions, "
        "r.total_quantity_sold, r.total_downtime_loss_cents, "
        "r.total_downtime_minutes, r.expected_cash_cents, r.actual_cash_cents, "
        "r.cash_difference_cents, r.expected_scan_cents, r.actual_scan_cents, "
        "r.scan_difference_cents, r.total_discrepancy_cents, r.discrepancy_note, "
        "r.machines_online, r.machines_offline, r.machines_in_downtime, "
        "r.machines_with_door_errors, r.machines_with_temp_alerts, "
        "r.reconciled, r.reconciled_at, u.username, r.note, r.created_at "
        "FROM daily_reports r LEFT JOIN users u ON u.id = r.operator_user_id ";

    char sql[2048];
    int use_date = 0, use_reconciled = 0;
    const char *date_val = NULL;
    int reconciled_val = -1;

    if (date != NULL && *date != '\0' && strlen(date) == 10) {
        use_date = 1; date_val = date;
    }
    if (reconciled != NULL && *reconciled != '\0') {
        if (strcmp(reconciled, "0") == 0 || strcmp(reconciled, "1") == 0) {
            use_reconciled = 1;
            reconciled_val = strcmp(reconciled, "1") == 0 ? 1 : 0;
        }
    }

    if (use_date || use_reconciled) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_date) {
            strcat(sql, "r.report_date = ? ");
            first = 0;
        }
        if (use_reconciled) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "r.reconciled = ? ");
        }
        strcat(sql, "ORDER BY r.id DESC LIMIT ?;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY r.id DESC LIMIT ?;", sql_base);
    }

    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询日报失败");
    }

    int idx = 1;
    if (use_date) sqlite3_bind_text(stmt, idx++, date_val, -1, SQLITE_TRANSIENT);
    if (use_reconciled) sqlite3_bind_int(stmt, idx++, reconciled_val);
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "report_date", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "total_sales_cents",
                            json_integer(sqlite3_column_int(stmt, 2)));
        json_object_set_new(it, "cash_sales_cents",
                            json_integer(sqlite3_column_int(stmt, 3)));
        json_object_set_new(it, "scan_sales_cents",
                            json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(it, "other_sales_cents",
                            json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(it, "total_transactions",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(it, "total_quantity_sold",
                            json_integer(sqlite3_column_int(stmt, 7)));
        json_object_set_new(it, "total_downtime_loss_cents",
                            json_integer(sqlite3_column_int(stmt, 8)));
        json_object_set_new(it, "total_downtime_minutes",
                            json_integer(sqlite3_column_int(stmt, 9)));
        json_object_set_new(it, "expected_cash_cents",
                            json_integer(sqlite3_column_int(stmt, 10)));
        json_object_set_new(it, "actual_cash_cents",
                            json_integer(sqlite3_column_int(stmt, 11)));
        json_object_set_new(it, "cash_difference_cents",
                            json_integer(sqlite3_column_int(stmt, 12)));
        json_object_set_new(it, "expected_scan_cents",
                            json_integer(sqlite3_column_int(stmt, 13)));
        json_object_set_new(it, "actual_scan_cents",
                            json_integer(sqlite3_column_int(stmt, 14)));
        json_object_set_new(it, "scan_difference_cents",
                            json_integer(sqlite3_column_int(stmt, 15)));
        json_object_set_new(it, "total_discrepancy_cents",
                            json_integer(sqlite3_column_int(stmt, 16)));
        json_object_set_new(it, "discrepancy_note",
                            json_string(safe_col_text(stmt, 17)));
        json_object_set_new(it, "machines_online",
                            json_integer(sqlite3_column_int(stmt, 18)));
        json_object_set_new(it, "machines_offline",
                            json_integer(sqlite3_column_int(stmt, 19)));
        json_object_set_new(it, "machines_in_downtime",
                            json_integer(sqlite3_column_int(stmt, 20)));
        json_object_set_new(it, "machines_with_door_errors",
                            json_integer(sqlite3_column_int(stmt, 21)));
        json_object_set_new(it, "machines_with_temp_alerts",
                            json_integer(sqlite3_column_int(stmt, 22)));
        json_object_set_new(it, "reconciled",
                            json_integer(sqlite3_column_int(stmt, 23)));
        json_object_set_new(it, "reconciled_at",
                            json_string(safe_col_text(stmt, 24)));
        json_object_set_new(it, "operator",
                            json_string(safe_col_text(stmt, 25)));
        json_object_set_new(it, "note",
                            json_string(safe_col_text(stmt, 26)));
        json_object_set_new(it, "created_at",
                            json_string(safe_col_text(stmt, 27)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取日报失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result handle_daily_report_reconcile(struct MHD_Connection *connection,
                                                  ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *report_date = NULL;
    if (require_string_field(body, "report_date", 10, &report_date) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "report_date 必填且格式为YYYY-MM-DD");
    }

    int actual_cash = 0, actual_scan = 0;
    if (parse_int_field(body, "actual_cash_cents", 0, 1000000000, &actual_cash) != 0 ||
        parse_int_field(body, "actual_scan_cents", 0, 1000000000, &actual_scan) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "actual_cash_cents/actual_scan_cents 必须为合法整数");
    }

    const char *discrepancy_note = optional_string_field(body, "discrepancy_note", 1024);
    const char *note = optional_string_field(body, "note", 1024);
    if (discrepancy_note == NULL || note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "discrepancy_note/note 需为字符串");
    }

    char report_date_copy[16];
    char discrepancy_copy[1025];
    char note_copy[1025];
    snprintf(report_date_copy, sizeof(report_date_copy), "%s", report_date);
    snprintf(discrepancy_copy, sizeof(discrepancy_copy), "%s",
             discrepancy_note != NULL ? discrepancy_note : "");
    snprintf(note_copy, sizeof(note_copy), "%s", note != NULL ? note : "");

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    if (!is_admin_role(&user)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_FORBIDDEN, "FORBIDDEN",
                            "仅管理员可对账");
    }

    sqlite3_stmt *stmt = NULL;
    int expected_cash = 0, expected_scan = 0;
    const char *find_sql =
        "SELECT id, expected_cash_cents, expected_scan_cents, reconciled "
        "FROM daily_reports WHERE report_date = ? LIMIT 1;";
    if (sqlite3_prepare_v2(g_db, find_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询日报失败");
    }
    sqlite3_bind_text(stmt, 1, report_date_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) {
        sqlite3_finalize(stmt);
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND",
                            "日报不存在，请先生成日报");
    }
    int report_id = sqlite3_column_int(stmt, 0);
    expected_cash = sqlite3_column_int(stmt, 1);
    expected_scan = sqlite3_column_int(stmt, 2);
    int already_reconciled = sqlite3_column_int(stmt, 3);
    sqlite3_finalize(stmt);

    if (already_reconciled) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_CONFLICT, "ALREADY_RECONCILED",
                            "该日报已对账");
    }

    int cash_diff = actual_cash - expected_cash;
    int scan_diff = actual_scan - expected_scan;
    int total_diff = cash_diff + scan_diff;

    const char *upd_sql =
        "UPDATE daily_reports SET actual_cash_cents = ?, cash_difference_cents = ?, "
        "actual_scan_cents = ?, scan_difference_cents = ?, "
        "total_discrepancy_cents = ?, discrepancy_note = ?, note = ?, "
        "reconciled = 1, reconciled_at = CURRENT_TIMESTAMP, "
        "operator_user_id = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?;";
    if (sqlite3_prepare_v2(g_db, upd_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "更新日报失败");
    }
    sqlite3_bind_int(stmt, 1, actual_cash);
    sqlite3_bind_int(stmt, 2, cash_diff);
    sqlite3_bind_int(stmt, 3, actual_scan);
    sqlite3_bind_int(stmt, 4, scan_diff);
    sqlite3_bind_int(stmt, 5, total_diff);
    sqlite3_bind_text(stmt, 6, discrepancy_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 7, note_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 8, user.user_id);
    sqlite3_bind_int(stmt, 9, report_id);
    rc = sqlite3_step(stmt);
    sqlite3_finalize(stmt);

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "对账失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "report_id", json_integer(report_id));
    json_object_set_new(data, "report_date", json_string(report_date_copy));
    json_object_set_new(data, "expected_cash_cents", json_integer(expected_cash));
    json_object_set_new(data, "actual_cash_cents", json_integer(actual_cash));
    json_object_set_new(data, "cash_difference_cents", json_integer(cash_diff));
    json_object_set_new(data, "expected_scan_cents", json_integer(expected_scan));
    json_object_set_new(data, "actual_scan_cents", json_integer(actual_scan));
    json_object_set_new(data, "scan_difference_cents", json_integer(scan_diff));
    json_object_set_new(data, "total_discrepancy_cents", json_integer(total_diff));
    json_object_set_new(data, "reconciled", json_integer(1));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_shift_reconcile(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    char err[256];
    json_t *body = NULL;
    if (parse_json_body(ci, &body, err) != 0) {
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_JSON", err);
    }

    const char *shift_date = NULL;
    const char *shift_type = NULL;
    if (require_string_field(body, "shift_date", 10, &shift_date) != 0 ||
        require_string_field(body, "shift_type", 16, &shift_type) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "shift_date/shift_type 必填");
    }

    if (strcmp(shift_type, "morning") != 0 && strcmp(shift_type, "afternoon") != 0 &&
        strcmp(shift_type, "evening") != 0 && strcmp(shift_type, "night") != 0 &&
        strcmp(shift_type, "daily") != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "shift_type 仅支持 morning/afternoon/evening/night/daily");
    }

    int actual_cash = 0, actual_scan = 0, actual_other = 0;
    if (parse_int_field(body, "actual_cash_cents", 0, 1000000000, &actual_cash) != 0 ||
        parse_int_field(body, "actual_scan_cents", 0, 1000000000, &actual_scan) != 0) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "actual_cash_cents/actual_scan_cents 必须为合法整数");
    }

    json_t *v = json_object_get(body, "actual_other_cents");
    if (json_is_integer(v)) {
        json_int_t n = json_integer_value(v);
        if (n >= 0) actual_other = (int)n;
    }

    const char *discrepancy_reason = optional_string_field(body, "discrepancy_reason", 1024);
    const char *note = optional_string_field(body, "note", 1024);
    if (discrepancy_reason == NULL || note == NULL) {
        json_decref(body);
        return respond_error(connection, MHD_HTTP_BAD_REQUEST, "INVALID_INPUT",
                            "discrepancy_reason/note 需为字符串");
    }

    char shift_date_copy[16];
    char shift_type_copy[17];
    char dr_copy[1025];
    char note_copy[1025];
    snprintf(shift_date_copy, sizeof(shift_date_copy), "%s", shift_date);
    snprintf(shift_type_copy, sizeof(shift_type_copy), "%s", shift_type);
    snprintf(dr_copy, sizeof(dr_copy), "%s",
             discrepancy_reason != NULL ? discrepancy_reason : "");
    snprintf(note_copy, sizeof(note_copy), "%s", note != NULL ? note : "");

    pthread_mutex_lock(&g_db_mutex);

    AuthUser user;
    char token_hash[TOKEN_HASH_HEX_LEN + 1] = {0};
    if (!authenticate_request(connection, &user, token_hash)) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_UNAUTHORIZED, "UNAUTHORIZED",
                            "需要登录");
    }

    int expected_cash = 0, expected_scan = 0, expected_other = 0;
    sqlite3_stmt *stmt = NULL;
    const char *sum_sql =
        "SELECT "
        "COALESCE(SUM(CASE WHEN payment_method='cash' THEN total_amount_cents ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN payment_method='scan' THEN total_amount_cents ELSE 0 END), 0), "
        "COALESCE(SUM(CASE WHEN payment_method='other' THEN total_amount_cents ELSE 0 END), 0) "
        "FROM machine_sales WHERE DATE(created_at) = ?;";
    if (sqlite3_prepare_v2(g_db, sum_sql, -1, &stmt, NULL) == SQLITE_OK) {
        sqlite3_bind_text(stmt, 1, shift_date_copy, -1, SQLITE_TRANSIENT);
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            expected_cash = sqlite3_column_int(stmt, 0);
            expected_scan = sqlite3_column_int(stmt, 1);
            expected_other = sqlite3_column_int(stmt, 2);
        }
        sqlite3_finalize(stmt);
    }

    int cash_diff = actual_cash - expected_cash;
    int scan_diff = actual_scan - expected_scan;
    int other_diff = actual_other - expected_other;
    int total_diff = cash_diff + scan_diff + other_diff;

    const char *ins_sql =
        "INSERT INTO shift_reconciliations (shift_date, shift_type, operator_user_id, "
        "expected_cash_cents, actual_cash_cents, cash_difference_cents, "
        "expected_scan_cents, actual_scan_cents, scan_difference_cents, "
        "expected_other_cents, actual_other_cents, other_difference_cents, "
        "total_discrepancy_cents, discrepancy_reason, note) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);";
    if (sqlite3_prepare_v2(g_db, ins_sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        json_decref(body);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "创建收班对账失败");
    }
    sqlite3_bind_text(stmt, 1, shift_date_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 2, shift_type_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 3, user.user_id);
    sqlite3_bind_int(stmt, 4, expected_cash);
    sqlite3_bind_int(stmt, 5, actual_cash);
    sqlite3_bind_int(stmt, 6, cash_diff);
    sqlite3_bind_int(stmt, 7, expected_scan);
    sqlite3_bind_int(stmt, 8, actual_scan);
    sqlite3_bind_int(stmt, 9, scan_diff);
    sqlite3_bind_int(stmt, 10, expected_other);
    sqlite3_bind_int(stmt, 11, actual_other);
    sqlite3_bind_int(stmt, 12, other_diff);
    sqlite3_bind_int(stmt, 13, total_diff);
    sqlite3_bind_text(stmt, 14, dr_copy, -1, SQLITE_TRANSIENT);
    sqlite3_bind_text(stmt, 15, note_copy, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt);
    int rec_id = (int)sqlite3_last_insert_rowid(g_db);
    sqlite3_finalize(stmt);

    pthread_mutex_unlock(&g_db_mutex);
    json_decref(body);

    if (rc != SQLITE_DONE) {
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "收班对账失败");
    }

    json_t *data = json_object();
    json_object_set_new(data, "reconciliation_id", json_integer(rec_id));
    json_object_set_new(data, "shift_date", json_string(shift_date_copy));
    json_object_set_new(data, "shift_type", json_string(shift_type_copy));
    json_object_set_new(data, "expected_cash_cents", json_integer(expected_cash));
    json_object_set_new(data, "actual_cash_cents", json_integer(actual_cash));
    json_object_set_new(data, "cash_difference_cents", json_integer(cash_diff));
    json_object_set_new(data, "expected_scan_cents", json_integer(expected_scan));
    json_object_set_new(data, "actual_scan_cents", json_integer(actual_scan));
    json_object_set_new(data, "scan_difference_cents", json_integer(scan_diff));
    json_object_set_new(data, "expected_other_cents", json_integer(expected_other));
    json_object_set_new(data, "actual_other_cents", json_integer(actual_other));
    json_object_set_new(data, "other_difference_cents", json_integer(other_diff));
    json_object_set_new(data, "total_discrepancy_cents", json_integer(total_diff));
    return respond_success(connection, MHD_HTTP_OK, data);
}

static enum MHD_Result handle_shift_reconciliation_list(struct MHD_Connection *connection) {
    pthread_mutex_lock(&g_db_mutex);

    const char *date =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "date");
    const char *shift_type =
        MHD_lookup_connection_value(connection, MHD_GET_ARGUMENT_KIND, "shift_type");
    int limit = parse_limit_query(connection);

    sqlite3_stmt *stmt = NULL;
    const char *sql_base =
        "SELECT s.id, s.shift_date, s.shift_type, s.expected_cash_cents, "
        "s.actual_cash_cents, s.cash_difference_cents, s.expected_scan_cents, "
        "s.actual_scan_cents, s.scan_difference_cents, s.expected_other_cents, "
        "s.actual_other_cents, s.other_difference_cents, s.total_discrepancy_cents, "
        "s.discrepancy_reason, s.note, u.username, s.created_at "
        "FROM shift_reconciliations s "
        "JOIN users u ON u.id = s.operator_user_id ";

    char sql[2048];
    int use_date = 0, use_type = 0;
    const char *date_val = NULL, *type_val = NULL;

    if (date != NULL && *date != '\0' && strlen(date) == 10) {
        use_date = 1; date_val = date;
    }
    if (shift_type != NULL && *shift_type != '\0' &&
        (strcmp(shift_type, "morning") == 0 || strcmp(shift_type, "afternoon") == 0 ||
        strcmp(shift_type, "evening") == 0 || strcmp(shift_type, "night") == 0 ||
        strcmp(shift_type, "daily") == 0)) {
        use_type = 1; type_val = shift_type;
    }

    if (use_date || use_type) {
        strcpy(sql, sql_base);
        strcat(sql, "WHERE ");
        int first = 1;
        if (use_date) {
            strcat(sql, "s.shift_date = ? ");
            first = 0;
        }
        if (use_type) {
            if (!first) strcat(sql, "AND ");
            strcat(sql, "s.shift_type = ? ");
        }
        strcat(sql, "ORDER BY s.id DESC LIMIT ?;");
    } else {
        snprintf(sql, sizeof(sql),
                 "%s ORDER BY s.id DESC LIMIT ?;", sql_base);
    }

    int idx = 1;
    if (sqlite3_prepare_v2(g_db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        pthread_mutex_unlock(&g_db_mutex);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "查询收班对账失败");
    }

    if (use_date) sqlite3_bind_text(stmt, idx++, date_val, -1, SQLITE_TRANSIENT);
    if (use_type) sqlite3_bind_text(stmt, idx++, type_val, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, idx, limit);

    json_t *items = json_array();
    int rc = SQLITE_OK;
    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
        json_t *it = json_object();
        json_object_set_new(it, "id", json_integer(sqlite3_column_int(stmt, 0)));
        json_object_set_new(it, "shift_date", json_string(safe_col_text(stmt, 1)));
        json_object_set_new(it, "shift_type", json_string(safe_col_text(stmt, 2)));
        json_object_set_new(it, "expected_cash_cents",
                            json_integer(sqlite3_column_int(stmt, 3)));
        json_object_set_new(it, "actual_cash_cents",
                            json_integer(sqlite3_column_int(stmt, 4)));
        json_object_set_new(it, "cash_difference_cents",
                            json_integer(sqlite3_column_int(stmt, 5)));
        json_object_set_new(it, "expected_scan_cents",
                            json_integer(sqlite3_column_int(stmt, 6)));
        json_object_set_new(it, "actual_scan_cents",
                            json_integer(sqlite3_column_int(stmt, 7)));
        json_object_set_new(it, "scan_difference_cents",
                            json_integer(sqlite3_column_int(stmt, 8)));
        json_object_set_new(it, "expected_other_cents",
                            json_integer(sqlite3_column_int(stmt, 9)));
        json_object_set_new(it, "actual_other_cents",
                            json_integer(sqlite3_column_int(stmt, 10)));
        json_object_set_new(it, "other_difference_cents",
                            json_integer(sqlite3_column_int(stmt, 11)));
        json_object_set_new(it, "total_discrepancy_cents",
                            json_integer(sqlite3_column_int(stmt, 12)));
        json_object_set_new(it, "discrepancy_reason",
                            json_string(safe_col_text(stmt, 13)));
        json_object_set_new(it, "note",
                            json_string(safe_col_text(stmt, 14)));
        json_object_set_new(it, "operator",
                            json_string(safe_col_text(stmt, 15)));
        json_object_set_new(it, "created_at",
                            json_string(safe_col_text(stmt, 16)));
        json_array_append_new(items, it);
    }

    sqlite3_finalize(stmt);
    pthread_mutex_unlock(&g_db_mutex);

    if (rc != SQLITE_DONE) {
        json_decref(items);
        return respond_error(connection, MHD_HTTP_INTERNAL_SERVER_ERROR,
                            "DB_ERROR", "读取收班对账失败");
    }

    return respond_success(connection, MHD_HTTP_OK, items);
}

static enum MHD_Result route_health(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    (void)ci;
    return handle_health(connection);
}

static enum MHD_Result route_register(struct MHD_Connection *connection,
                                      ConnectionInfo *ci) {
    return handle_register(connection, ci);
}

static enum MHD_Result route_login(struct MHD_Connection *connection,
                                   ConnectionInfo *ci) {
    return handle_login(connection, ci);
}

static enum MHD_Result route_logout(struct MHD_Connection *connection,
                                    ConnectionInfo *ci) {
    (void)ci;
    return handle_logout(connection);
}

static enum MHD_Result route_auth_me(struct MHD_Connection *connection,
                                     ConnectionInfo *ci) {
    (void)ci;
    return handle_auth_me(connection);
}

static enum MHD_Result route_create_product(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_create_product(connection, ci);
}

static enum MHD_Result route_list_products(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    (void)ci;
    return handle_list_products(connection);
}

static enum MHD_Result route_inbound(struct MHD_Connection *connection,
                                     ConnectionInfo *ci) {
    return handle_inbound(connection, ci);
}

static enum MHD_Result route_sales(struct MHD_Connection *connection,
                                   ConnectionInfo *ci) {
    return handle_sales(connection, ci);
}

static enum MHD_Result route_inventory(struct MHD_Connection *connection,
                                       ConnectionInfo *ci) {
    (void)ci;
    return handle_inventory(connection);
}

static enum MHD_Result route_movements(struct MHD_Connection *connection,
                                       ConnectionInfo *ci) {
    (void)ci;
    return handle_movements(connection);
}

static enum MHD_Result route_openapi_doc(struct MHD_Connection *connection,
                                         ConnectionInfo *ci);

static enum MHD_Result route_swagger_ui(struct MHD_Connection *connection,
                                        ConnectionInfo *ci) {
    (void)ci;
    return docs_send_swagger_ui(connection);
}

static enum MHD_Result route_create_machine(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_create_machine(connection, ci);
}

static enum MHD_Result route_list_machines(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    (void)ci;
    return handle_list_machines(connection);
}

static enum MHD_Result route_update_machine(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_update_machine(connection, ci);
}

static enum MHD_Result route_delete_machine(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_delete_machine(connection, ci);
}

static enum MHD_Result route_machine_stock_add(struct MHD_Connection *connection,
                                               ConnectionInfo *ci) {
    return handle_machine_stock_add(connection, ci);
}

static enum MHD_Result route_machine_stock_list(struct MHD_Connection *connection,
                                                ConnectionInfo *ci) {
    (void)ci;
    return handle_machine_stock_list(connection);
}

static enum MHD_Result route_machine_sale(struct MHD_Connection *connection,
                                          ConnectionInfo *ci) {
    return handle_machine_sale(connection, ci);
}

static enum MHD_Result route_machine_sales_list(struct MHD_Connection *connection,
                                                ConnectionInfo *ci) {
    (void)ci;
    return handle_machine_sales_list(connection);
}

static enum MHD_Result route_downtime_start(struct MHD_Connection *connection,
                                            ConnectionInfo *ci) {
    return handle_downtime_start(connection, ci);
}

static enum MHD_Result route_downtime_end(struct MHD_Connection *connection,
                                          ConnectionInfo *ci) {
    return handle_downtime_end(connection, ci);
}

static enum MHD_Result route_downtime_list(struct MHD_Connection *connection,
                                           ConnectionInfo *ci) {
    (void)ci;
    return handle_downtime_list(connection);
}

static enum MHD_Result route_replenishment_generate(struct MHD_Connection *connection,
                                                    ConnectionInfo *ci) {
    return handle_replenishment_generate(connection, ci);
}

static enum MHD_Result route_replenishment_list(struct MHD_Connection *connection,
                                                ConnectionInfo *ci) {
    (void)ci;
    return handle_replenishment_list(connection);
}

static enum MHD_Result route_replenishment_complete_item(struct MHD_Connection *connection,
                                                         ConnectionInfo *ci) {
    return handle_replenishment_complete_item(connection, ci);
}

static enum MHD_Result route_daily_report_generate(struct MHD_Connection *connection,
                                                   ConnectionInfo *ci) {
    return handle_daily_report_generate(connection, ci);
}

static enum MHD_Result route_daily_report_list(struct MHD_Connection *connection,
                                               ConnectionInfo *ci) {
    (void)ci;
    return handle_daily_report_list(connection);
}

static enum MHD_Result route_daily_report_reconcile(struct MHD_Connection *connection,
                                                    ConnectionInfo *ci) {
    return handle_daily_report_reconcile(connection, ci);
}

static enum MHD_Result route_shift_reconcile(struct MHD_Connection *connection,
                                             ConnectionInfo *ci) {
    return handle_shift_reconcile(connection, ci);
}

static enum MHD_Result route_shift_reconciliation_list(struct MHD_Connection *connection,
                                                       ConnectionInfo *ci) {
    (void)ci;
    return handle_shift_reconciliation_list(connection);
}

static enum MHD_Result route_home(struct MHD_Connection *connection,
                                  ConnectionInfo *ci) {
    (void)ci;
    return docs_send_home(connection);
}

static const ApiRoute g_api_routes[] = {
    {MHD_HTTP_METHOD_GET, "/", route_home, "Home", "服务首页", "System", 0, 0, 0},
    {MHD_HTTP_METHOD_GET, "/api/v1/health", route_health, "Health Check",
     "服务健康检查", "System", 0, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/auth/register", route_register, "Create User",
     "创建用户（需管理员鉴权）", "Auth", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/auth/login", route_login, "Login",
     "用户登录并获取访问令牌", "Auth", 0, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/auth/logout", route_logout, "Logout",
     "当前令牌退出登录", "Auth", 1, 0, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/auth/me", route_auth_me, "Current User",
     "获取当前登录用户信息", "Auth", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/products", route_create_product,
     "Create Product", "新增商品（管理员）", "Product", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/products", route_list_products, "List Products",
     "查询商品列表", "Product", 0, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/inbound", route_inbound, "Inbound",
     "入库（进货）", "Inventory", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/sales", route_sales, "Sales",
     "销售出库", "Inventory", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/inventory", route_inventory, "Inventory Summary",
     "库存汇总与明细", "Inventory", 0, 0, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/movements", route_movements, "Movement History",
     "库存流水查询", "Inventory", 1, 0, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/openapi.json", route_openapi_doc,
     "OpenAPI Document", "自动生成的 OpenAPI 文档", "System", 0, 0, 1},
    {MHD_HTTP_METHOD_GET, "/docs", route_swagger_ui, "Swagger UI",
     "Swagger 交互式文档页面", "System", 0, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/machines", route_create_machine,
     "Create Machine", "新增售货机（管理员）", "Machine", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/machines", route_list_machines,
     "List Machines", "查询售货机列表，支持状态/异常过滤", "Machine", 1, 0, 1},
    {MHD_HTTP_METHOD_PUT, "/api/v1/machines", route_update_machine,
     "Update Machine", "更新售货机信息", "Machine", 1, 1, 1},
    {MHD_HTTP_METHOD_DELETE, "/api/v1/machines", route_delete_machine,
     "Delete Machine", "删除售货机（管理员）", "Machine", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/machines/stock/add", route_machine_stock_add,
     "Machine Stock Add", "售货机补货入库", "Machine", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/machines/stock", route_machine_stock_list,
     "Machine Stock List", "查询售货机库存，支持低库存过滤", "Machine", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/machines/sale", route_machine_sale,
     "Machine Sale", "售货机销售出库，支持现金/扫码", "Machine", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/machines/sales", route_machine_sales_list,
     "Machine Sales List", "查询售货机销售记录", "Machine", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/downtime/start", route_downtime_start,
     "Start Downtime", "开始停机记录", "Downtime", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/downtime/end", route_downtime_end,
     "End Downtime", "结束停机并计算损失", "Downtime", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/downtime", route_downtime_list,
     "List Downtime", "查询停机记录", "Downtime", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/replenishment/generate", route_replenishment_generate,
     "Generate Replenishment Route", "生成补货路线，按优先级排序", "Replenishment", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/replenishment", route_replenishment_list,
     "List Replenishment Routes", "查询补货路线，支持明细查询", "Replenishment", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/replenishment/complete", route_replenishment_complete_item,
     "Complete Replenishment Item", "完成补货路线单项", "Replenishment", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/daily-report/generate", route_daily_report_generate,
     "Generate Daily Report", "生成日报表", "Report", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/daily-report", route_daily_report_list,
     "List Daily Reports", "查询日报表", "Report", 1, 0, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/daily-report/reconcile", route_daily_report_reconcile,
     "Reconcile Daily Report", "日报对账（管理员）", "Report", 1, 1, 1},
    {MHD_HTTP_METHOD_POST, "/api/v1/shift-reconcile", route_shift_reconcile,
     "Shift Reconcile", "收班对账，核对现金/扫码/异常差额", "Report", 1, 1, 1},
    {MHD_HTTP_METHOD_GET, "/api/v1/shift-reconciliations", route_shift_reconciliation_list,
     "List Shift Reconciliations", "查询收班对账记录", "Report", 1, 0, 1},
};

static const size_t g_api_routes_count =
    sizeof(g_api_routes) / sizeof(g_api_routes[0]);

static enum MHD_Result route_openapi_doc(struct MHD_Connection *connection,
                                         ConnectionInfo *ci) {
    (void)ci;
    return docs_send_openapi(connection, g_api_routes, g_api_routes_count);
}

static enum MHD_Result handle_options(struct MHD_Connection *connection) {
    struct MHD_Response *response =
        MHD_create_response_from_buffer(0, "", MHD_RESPMEM_PERSISTENT);
    if (response == NULL) {
        return MHD_NO;
    }

    MHD_add_response_header(response, "Access-Control-Allow-Origin", "*");
    MHD_add_response_header(response, "Access-Control-Allow-Headers",
                            "Content-Type, Authorization");
    MHD_add_response_header(response, "Access-Control-Allow-Methods",
                            "GET, POST, OPTIONS");

    enum MHD_Result ret = MHD_queue_response(connection, MHD_HTTP_NO_CONTENT, response);
    MHD_destroy_response(response);
    return ret;
}

static enum MHD_Result route_request(struct MHD_Connection *connection,
                                     const char *url, const char *method,
                                     ConnectionInfo *ci) {
    if (strcmp(method, MHD_HTTP_METHOD_OPTIONS) == 0) {
        return handle_options(connection);
    }

    for (size_t i = 0; i < g_api_routes_count; ++i) {
        if (strcmp(method, g_api_routes[i].method) == 0 &&
            strcmp(url, g_api_routes[i].path) == 0) {
            return g_api_routes[i].handler(connection, ci);
        }
    }

    return respond_error(connection, MHD_HTTP_NOT_FOUND, "NOT_FOUND", "接口不存在");
}

static enum MHD_Result request_handler(void *cls,
                                       struct MHD_Connection *connection,
                                       const char *url, const char *method,
                                       const char *version,
                                       const char *upload_data,
                                       size_t *upload_data_size, void **con_cls) {
    (void)cls;
    (void)version;

    ConnectionInfo *ci = (ConnectionInfo *)(*con_cls);
    if (ci == NULL) {
        ci = (ConnectionInfo *)calloc(1, sizeof(ConnectionInfo));
        if (ci == NULL) {
            return MHD_NO;
        }
        *con_cls = ci;
        return MHD_YES;
    }

    if (is_method_with_body(method) && *upload_data_size != 0) {
        if (append_body(ci, upload_data, *upload_data_size) != 0) {
            *upload_data_size = 0;
            return respond_error(connection, MHD_HTTP_CONTENT_TOO_LARGE,
                                "PAYLOAD_TOO_LARGE", "请求体超过限制");
        }

        *upload_data_size = 0;
        return MHD_YES;
    }

    if (ci->processed) {
        return MHD_YES;
    }
    ci->processed = 1;

    return route_request(connection, url, method, ci);
}

static void request_completed_callback(void *cls, struct MHD_Connection *connection,
                                       void **con_cls,
                                       enum MHD_RequestTerminationCode toe) {
    (void)cls;
    (void)connection;
    (void)toe;

    ConnectionInfo *ci = (ConnectionInfo *)(*con_cls);
    if (ci != NULL) {
        free(ci->body);
        free(ci);
        *con_cls = NULL;
    }
}

static void load_config(void) {
    g_cfg.port = env_to_int("PORT", DEFAULT_PORT);
    g_cfg.session_ttl_hours =
        env_to_int("SESSION_TTL_HOURS", DEFAULT_SESSION_TTL_HOURS);
    g_cfg.db_path = getenv("DB_PATH");
    if (g_cfg.db_path == NULL || *g_cfg.db_path == '\0') {
        g_cfg.db_path = DEFAULT_DB_PATH;
    }

    g_cfg.key_file = getenv("USER_DATA_KEY_FILE");
    if (g_cfg.key_file == NULL || *g_cfg.key_file == '\0') {
        g_cfg.key_file = DEFAULT_KEY_FILE;
    }
}

int main(void) {
    signal(SIGINT, handle_signal);
    signal(SIGTERM, handle_signal);

    load_config();

    if (sodium_init() < 0) {
        fprintf(stderr, "[FATAL] libsodium 初始化失败\n");
        return 1;
    }

    if (db_init() != 0) {
        fprintf(stderr, "[FATAL] 数据库初始化失败\n");
        return 1;
    }

    if (load_or_create_key() != 0) {
        fprintf(stderr, "[FATAL] 用户字段加密密钥初始化失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    if (ensure_default_admin_user() != 0) {
        fprintf(stderr, "[FATAL] 默认管理员初始化失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    if (ensure_seed_stock_movement_consistency() != 0) {
        fprintf(stderr, "[FATAL] 种子库存流水修复失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    struct MHD_Daemon *daemon = MHD_start_daemon(
        MHD_USE_INTERNAL_POLLING_THREAD, (uint16_t)g_cfg.port, NULL, NULL,
        &request_handler, NULL, MHD_OPTION_NOTIFY_COMPLETED,
        request_completed_callback, NULL, MHD_OPTION_END);

    if (daemon == NULL) {
        fprintf(stderr, "[FATAL] HTTP 服务启动失败\n");
        sqlite3_close(g_db);
        return 1;
    }

    fprintf(stdout,
            "[INFO] 服务启动成功\n"
            "[INFO] 端口: %d\n"
            "[INFO] 数据库: %s\n"
            "[INFO] 会话时长(小时): %d\n",
            g_cfg.port, g_cfg.db_path, g_cfg.session_ttl_hours);

    while (g_running) {
        sleep(1);
    }

    MHD_stop_daemon(daemon);
    sqlite3_close(g_db);
    pthread_mutex_destroy(&g_db_mutex);

    fprintf(stdout, "[INFO] 服务已停止\n");
    return 0;
}
