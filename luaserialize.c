/* Lua CJSON - JSON support for Lua
 *
 * Copyright (c) 2010-2012  Mark Pulford <mark@kyne.com.au>
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/* Caveats:
 * - JSON "null" values are represented as lightuserdata since Lua
 *   tables cannot contain "nil". Compare with cjson.null.
 * - Invalid UTF-8 characters are not detected and will be passed
 *   untouched. If required, UTF-8 error checking should be done
 *   outside this library.
 * - Javascript comments are not part of the JSON spec, and are not
 *   currently supported.
 *
 * Note: Decoding is slower than encoding. Lua spends significant
 *       time (30%) managing tables when parsing JSON since it is
 *       difficult to know object/array sizes ahead of time.
 */

#include <assert.h>
#include <string.h>
#include <math.h>
#include <limits.h>
#include <lua.h>
#include <lualib.h>
#include <lauxlib.h>
#include <lobject.h>
#include <stdbool.h>

#include "strbuf.h"
#include "fpconv.h"

#ifndef CJSON_MODNAME
#define CJSON_MODNAME   "cjson"
#endif

#ifndef CJSON_VERSION
#define CJSON_VERSION   "2.1devel"
#endif

/* Workaround for Solaris platforms missing isinf() */
#if !defined(isinf) && (defined(USE_INTERNAL_ISINF) || defined(MISSING_ISINF))
#define isinf(x) (!isnan(x) && isnan((x) - (x)))
#endif

#define DEFAULT_SPARSE_CONVERT 0
#define DEFAULT_SPARSE_RATIO 2
#define DEFAULT_SPARSE_SAFE 10
#define DEFAULT_ENCODE_MAX_DEPTH 1000
#define DEFAULT_DECODE_MAX_DEPTH 1000
#define DEFAULT_ENCODE_INVALID_NUMBERS 0
#define DEFAULT_DECODE_INVALID_NUMBERS 1
#define DEFAULT_ENCODE_KEEP_BUFFER 1
#define DEFAULT_ENCODE_NUMBER_PRECISION 14

#ifdef DISABLE_INVALID_NUMBERS
#undef DEFAULT_DECODE_INVALID_NUMBERS
#define DEFAULT_DECODE_INVALID_NUMBERS 0
#endif


static const char reserved_keywords[][20] = {
   "and", "break", "do", "else", "elseif", "end", "false", "for",
    "function", "if", "in", "local", "nil", "not", "or", "repeat",
    "return", "then", "true", "until", "while"
};

bool find_reserved_word(const char *word)
{
  int l = 0;
  int r = 20;
  while(l < r)
  {
    int mid = (l + r) / 2;
    int result = strcmp(word, reserved_keywords[mid]);
    if(result < 0)
    {
      r = mid;
    }
    else if (result == 0)
    {
      return true;
    }
    else
    {
      l = mid + 1;
    }
  }
  if(strcmp(word, reserved_keywords[l]) != 0)
  {
    return false;
  }
  return true;
}

bool check_key_word(const char *str, int str_len)
{
    bool need_para = false;
    if(str_len == 0 || !((str[0] >= 'a' && str[0] <= 'z') || (str[0] >= 'A' && str[0] <= 'Z') || (str[0] == '_')))
    {
        need_para = true;
    }
    for(int i = 0; i < str_len; ++i)
    {
        if(!((str[i] >= 'a' && str[i] <= 'z') || (str[i] >= 'A' && str[i] <= 'Z') || (str[i] == '_') || (str[i] >= '0' && str[i] <= '9')))
        {
            need_para = true;
        }
    }
    if(!need_para && find_reserved_word(str))
    {
        need_para = true;
    }
    return need_para;
}

typedef struct node_value 
{
  union 
  {
    struct{    
      const char *s;
      size_t len;
    }s;
    long long i;
    bool b;
    double d;
  } value;
  int type;
}node_Value;

typedef struct node_value_list
{
  node_Value *list;
  int capacity;
  int length;
}node_value_List;


static void node_value_list_init(node_value_List *list, int capacity)
{
  list->list = malloc(sizeof(node_Value) * capacity);
  memset(list->list, 0, sizeof(node_Value) * capacity);
  list->capacity = capacity;
  list->length = 0;
}

static void node_value_list_resize(node_value_List *list, int capacity)
{
  list->list = realloc(list->list, sizeof(node_Value) * capacity);
  list->capacity = capacity;
}

static void node_value_list_push(node_value_List *list, node_Value v)
{
  if(list->length >= list->capacity)
  {
    node_value_list_resize(list, list->length * 2);
  }
  list->list[list->length++] = v;
}

static node_Value* get_node_value(node_value_List *list)
{
  if(++list->length >= list->capacity)
  {
    node_value_list_resize(list, list->length * 2);
  }
  return list->list+list->length;
}


static int l_strcmp (const node_Value *ls, const node_Value *rs) {
  const char *l = ls->value.s.s;
  size_t ll = ls->value.s.len;
  const char *r = rs->value.s.s;
  size_t lr = rs->value.s.len;
  for (;;) {  /* for each segment */
    int temp = strcoll(l, r);
    if (temp != 0)  /* not equal? */
      return temp;  /* done */
    else {  /* strings are equal up to a '\0' */
      size_t len = strlen(l);  /* index of first '\0' in both strings */
      if (len == lr)  /* 'rs' is finished? */
        return (len == ll) ? 0 : 1;  /* check 'ls' */
      else if (len == ll)  /* 'ls' is finished? */
        return -1;  /* 'ls' is less than 'rs' ('rs' is not finished) */
      /* both strings longer than 'len'; go on comparing after the '\0' */
      len++;
      l += len; ll -= len; r += len; lr -= len;
    }
  }
}



static int node_value_compare(const void *a, const void *b)
{
  node_Value *aa = (node_Value*)a;
  node_Value *bb = (node_Value*)b;
  if(aa->type != bb->type)
  {
    return aa->type - bb->type; 
  }
  switch (aa->type)
  { 
  case LUA_TLIGHTUSERDATA:
    return aa->value.i - bb->value.i;
    break;
  case LUA_TNUMBER:
    return aa->value.d - bb->value.d;
    break;
  case LUA_TBOOLEAN:
    return aa->value.b - bb->value.b;
    break;
  case LUA_TSTRING:
    return l_strcmp(aa, bb);
    break;
  default:
    //luaL_error(L, "error key type %d, typename:%s\n", aa->type, lua_typename(L, aa->type));
    printf("error key type %d\n", aa->type);
    exit(-1);
    break;
  }
  return 0;
}

static void node_value_list_release(node_value_List *list)
{
  free(list->list);
}

static void node_value_list_sort(node_value_List *list)
{
  qsort(list->list, list->length, sizeof(node_Value), node_value_compare);
}

static bool is_order = true;

typedef struct {
    char escape2char[256];  /* Decoding */

    /* encode_buf is only allocated and used when
     * encode_keep_buffer is set */
    strbuf_t encode_buf;

    int encode_sparse_convert;
    int encode_sparse_ratio;
    int encode_sparse_safe;
    int encode_max_depth;
    int encode_invalid_numbers;     /* 2 => Encode as "null" */
    int encode_number_precision;
    int encode_keep_buffer;

    int decode_invalid_numbers;
    int decode_max_depth;
} json_config_t;

typedef struct {
    const char *data;
    const char *ptr;
    strbuf_t *tmp;    /* Temporary storage for strings */
    json_config_t *cfg;
    int current_depth;
} json_parse_t;

typedef struct {
    int index;
    union {
        const char *string;
        double number;
        lua_Integer integer;
        int boolean;
    } value;
    int string_len;
} json_token_t;

static const char *char2escape[256] = {
    "\\u0000", "\\u0001", "\\u0002", "\\u0003",
    "\\u0004", "\\u0005", "\\u0006", "\\u0007",
    "\\b", "\\t", "\\n", "\\u000b",
    "\\f", "\\r", "\\u000e", "\\u000f",
    "\\u0010", "\\u0011", "\\u0012", "\\u0013",
    "\\u0014", "\\u0015", "\\u0016", "\\u0017",
    "\\u0018", "\\u0019", "\\u001a", "\\u001b",
    "\\u001c", "\\u001d", "\\u001e", "\\u001f",
    NULL, NULL, "\\\"", NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, "\\\\", NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, "\\u007f",
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
};

//
static const char *charspace = "                                               ";

/* ===== CONFIGURATION ===== */

static json_config_t *json_fetch_config(lua_State *l)
{
    json_config_t *cfg;

    cfg = lua_touserdata(l, lua_upvalueindex(1));
    if (!cfg)
        luaL_error(l, "BUG: Unable to fetch CJSON configuration");

    return cfg;
}

/* Ensure the correct number of arguments have been provided.
 * Pad with nil to allow other functions to simply check arg[i]
 * to find whether an argument was provided */
static json_config_t *json_arg_init(lua_State *l, int args)
{
    luaL_argcheck(l, lua_gettop(l) <= args, args + 1,
                  "found too many arguments");

    while (lua_gettop(l) < args)
        lua_pushnil(l);

    return json_fetch_config(l);
}

/* Process integer options for configuration functions */
static int json_integer_option(lua_State *l, int optindex, int *setting,
                               int min, int max)
{
    char errmsg[64];
    int value;

    if (!lua_isnil(l, optindex)) {
        value = luaL_checkinteger(l, optindex);
        snprintf(errmsg, sizeof(errmsg), "expected integer between %d and %d", min, max);
        luaL_argcheck(l, min <= value && value <= max, 1, errmsg);
        *setting = value;
    }

    lua_pushinteger(l, *setting);

    return 1;
}

/* Process enumerated arguments for a configuration function */
static int json_enum_option(lua_State *l, int optindex, int *setting,
                            const char **options, int bool_true)
{
    static const char *bool_options[] = { "off", "on", NULL };

    if (!options) {
        options = bool_options;
        bool_true = 1;
    }

    if (!lua_isnil(l, optindex)) {
        if (bool_true && lua_isboolean(l, optindex))
            *setting = lua_toboolean(l, optindex) * bool_true;
        else
            *setting = luaL_checkoption(l, optindex, NULL, options);
    }

    if (bool_true && (*setting == 0 || *setting == bool_true))
        lua_pushboolean(l, *setting);
    else
        lua_pushstring(l, options[*setting]);

    return 1;
}

/* Configures handling of extremely sparse arrays:
 * convert: Convert extremely sparse arrays into objects? Otherwise error.
 * ratio: 0: always allow sparse; 1: never allow sparse; >1: use ratio
 * safe: Always use an array when the max index <= safe */
static int json_cfg_encode_sparse_array(lua_State *l)
{
    json_config_t *cfg = json_arg_init(l, 3);

    json_enum_option(l, 1, &cfg->encode_sparse_convert, NULL, 1);
    json_integer_option(l, 2, &cfg->encode_sparse_ratio, 0, INT_MAX);
    json_integer_option(l, 3, &cfg->encode_sparse_safe, 0, INT_MAX);

    return 3;
}


/* Configures number precision when converting doubles to text */
static int json_cfg_encode_number_precision(lua_State *l)
{
    json_config_t *cfg = json_arg_init(l, 1);

    return json_integer_option(l, 1, &cfg->encode_number_precision, 1, 14);
}

/* Configures JSON encoding buffer persistence */
static int json_cfg_encode_keep_buffer(lua_State *l)
{
    json_config_t *cfg = json_arg_init(l, 1);
    int old_value;

    old_value = cfg->encode_keep_buffer;

    json_enum_option(l, 1, &cfg->encode_keep_buffer, NULL, 1);

    /* Init / free the buffer if the setting has changed */
    if (old_value ^ cfg->encode_keep_buffer) {
        if (cfg->encode_keep_buffer)
            strbuf_init(&cfg->encode_buf, 0);
        else
            strbuf_free(&cfg->encode_buf);
    }

    return 1;
}

#if defined(DISABLE_INVALID_NUMBERS) && !defined(USE_INTERNAL_FPCONV)
void json_verify_invalid_number_setting(lua_State *l, int *setting)
{
    if (*setting == 1) {
        *setting = 0;
        luaL_error(l, "Infinity, NaN, and/or hexadecimal numbers are not supported.");
    }
}
#else
#define json_verify_invalid_number_setting(l, s)    do { } while(0)
#endif


static int json_destroy_config(lua_State *l)
{
    json_config_t *cfg;

    cfg = lua_touserdata(l, 1);
    if (cfg)
        strbuf_free(&cfg->encode_buf);
    cfg = NULL;

    return 0;
}

static void json_create_config(lua_State *l)
{
    json_config_t *cfg;
    int i;

    cfg = lua_newuserdata(l, sizeof(*cfg));

    /* Create GC method to clean up strbuf */
    lua_newtable(l);
    lua_pushcfunction(l, json_destroy_config);
    lua_setfield(l, -2, "__gc");
    lua_setmetatable(l, -2);

    cfg->encode_sparse_convert = DEFAULT_SPARSE_CONVERT;
    cfg->encode_sparse_ratio = DEFAULT_SPARSE_RATIO;
    cfg->encode_sparse_safe = DEFAULT_SPARSE_SAFE;
    cfg->encode_max_depth = DEFAULT_ENCODE_MAX_DEPTH;
    cfg->decode_max_depth = DEFAULT_DECODE_MAX_DEPTH;
    cfg->encode_invalid_numbers = DEFAULT_ENCODE_INVALID_NUMBERS;
    cfg->decode_invalid_numbers = DEFAULT_DECODE_INVALID_NUMBERS;
    cfg->encode_keep_buffer = DEFAULT_ENCODE_KEEP_BUFFER;
    cfg->encode_number_precision = DEFAULT_ENCODE_NUMBER_PRECISION;

#if DEFAULT_ENCODE_KEEP_BUFFER > 0
    strbuf_init(&cfg->encode_buf, 0);
#endif
}

    
/* ===== ENCODING ===== */

static void json_encode_exception(lua_State *l, json_config_t *cfg, strbuf_t *json, int lindex,
                                  const char *reason)
{
    if (!cfg->encode_keep_buffer)
        strbuf_free(json);
    luaL_error(l, "Cannot serialise %s: %s",
                  lua_typename(l, lua_type(l, lindex)), reason);
}

/* json_append_string args:
 * - lua_State
 * - JSON strbuf
 * - String (Lua stack index)
 *
 * Returns nothing. Doesn't remove string from Lua stack */
static void json_append_string(lua_State *l, strbuf_t *json, int lindex, int quoted)
{
    const char *escstr;
    int i;
    const char *str;
    size_t len;

    str = lua_tolstring(l, lindex, &len);

    /* Worst case is len * 6 (all unicode escapes).
     * This buffer is reused constantly for small strings
     * If there are any excess pages, they won't be hit anyway.
     * This gains ~5% speedup. */
    strbuf_ensure_empty_length(json, len * 6 + 4);

    if (quoted)
    {
        if (quoted == 2)
            strbuf_append_char_unsafe(json, '[');
        strbuf_append_char_unsafe(json, '\"');
    }
    for (i = 0; i < len; i++) {
        escstr = char2escape[(unsigned char)str[i]];
        if (escstr)
            strbuf_append_string(json, escstr);
        else
            strbuf_append_char_unsafe(json, str[i]);
    }
    if (quoted)
    {
        strbuf_append_char_unsafe(json, '\"');
        if (quoted == 2)
            strbuf_append_char_unsafe(json, ']');
    }
}

static int sort_keys(lua_State *l, json_config_t *cfg, strbuf_t *json, node_value_List* list)
{
    node_Value v;
    lua_pushnil(l);
    /* table, startkey */
    while (lua_next(l, -2) != 0) {
        /* table, key, value */
        int keytype = lua_type(l, -2);
        switch (keytype)
        {
        case LUA_TBOOLEAN:
            v.type = keytype;
            v.value.b = lua_toboolean(l, -2);
            break;
        case LUA_TNUMBER:
            if(lua_isinteger(l, -2))
            {
                v.type = LUA_TNUMBER;
                v.value.i = lua_tointeger(l, -2);
            }
            else
            {
                // v.type = LUA_TNUMBER;
                // v.value.d = lua_tonumber(l, -2);
                luaL_error(l, "error key type %d, typename: %s\n", keytype, lua_typename(l, keytype));
            }
            break;
        case LUA_TSTRING:
            v.type = keytype;
            v.value.s.s = lua_tolstring(l, -2, &(v.value.s.len));
            break;
        default:
            luaL_error(l, "error key type %d, typename: %s\n", keytype, lua_typename(l, keytype));
            break;
        }
        node_value_list_push(list, v);
        lua_pop(l, 1);

    }
    node_value_list_sort(list);

    return 1;
}

static void json_check_encode_depth(lua_State *l, json_config_t *cfg,
                                    int current_depth, strbuf_t *json)
{
    /* Ensure there are enough slots free to traverse a table (key,
     * value) and push a string for a potential error message.
     *
     * Unlike "decode", the key and value are still on the stack when
     * lua_checkstack() is called.  Hence an extra slot for luaL_error()
     * below is required just in case the next check to lua_checkstack()
     * fails.
     *
     * While this won't cause a crash due to the EXTRA_STACK reserve
     * slots, it would still be an improper use of the API. */
    if (current_depth <= cfg->encode_max_depth && lua_checkstack(l, 3))
        return;

    if (!cfg->encode_keep_buffer)
        strbuf_free(json);

    luaL_error(l, "Cannot serialise, excessive nesting (%d)",
               current_depth);
}

static void json_append_data(lua_State *l, json_config_t *cfg,
                             int current_depth, strbuf_t *json);

/* json_append_array args:
 * - lua_State
 * - JSON strbuf
 * - Size of passwd Lua array (top of stack) */
static void json_append_array(lua_State *l, json_config_t *cfg, int current_depth,
                              strbuf_t *json, int array_length)
{
    int comma, i;

    strbuf_append_mem(json, "{\n", 2);

    comma = 0;
    for (i = 1; i <= array_length; i++) {
        
        int vt = lua_rawgeti(l, -1, i);
        if (vt == LUA_TNIL) {
            lua_pop(l, 1);
        }
        else
        {
            if (comma) {
                strbuf_append_mem(json, ",\n", 2);
            }
            else
                comma = 1;

            //
            strbuf_append_mem(json, charspace, current_depth*2);

            // lua_rawgeti(l, -1, i);
            json_append_data(l, cfg, current_depth, json);
            // strbuf_append_char(json, ',');
            // strbuf_append_char(json, '\n');
            lua_pop(l, 1);
        }
    }

    strbuf_append_char(json, '\n');
    strbuf_append_mem(json, charspace, (current_depth-1)*2);
    strbuf_append_char(json, '}');
}

static void json_append_number(lua_State *l, json_config_t *cfg,
                               strbuf_t *json, int lindex)
{
    int len;
#if LUA_VERSION_NUM >= 503
    if (lua_isinteger(l, lindex)) {
        lua_Integer num = lua_tointeger(l, lindex);
        strbuf_ensure_empty_length(json, FPCONV_G_FMT_BUFSIZE); /* max length of int64 is 19 */
        len = sprintf(strbuf_empty_ptr(json), LUA_INTEGER_FMT, num);
        strbuf_extend_length(json, len);
        return;
    }
#endif
    double num = lua_tonumber(l, lindex);

    if (cfg->encode_invalid_numbers == 0) {
        /* Prevent encoding invalid numbers */
        if (isinf(num) || isnan(num))
            json_encode_exception(l, cfg, json, lindex,
                                  "must not be NaN or Infinity");
    } else if (cfg->encode_invalid_numbers == 1) {
        /* Encode NaN/Infinity separately to ensure Javascript compatible
         * values are used. */
        if (isnan(num)) {
            strbuf_append_mem(json, "NaN", 3);
            return;
        }
        if (isinf(num)) {
            if (num < 0)
                strbuf_append_mem(json, "-Infinity", 9);
            else
                strbuf_append_mem(json, "Infinity", 8);
            return;
        }
    } else {
        /* Encode invalid numbers as "null" */
        if (isinf(num) || isnan(num)) {
            strbuf_append_mem(json, "null", 4);
            return;
        }
    }

    strbuf_ensure_empty_length(json, FPCONV_G_FMT_BUFSIZE);
    len = fpconv_g_fmt(strbuf_empty_ptr(json), num, cfg->encode_number_precision);
    strbuf_extend_length(json, len);
}

static void json_append_object(lua_State *l, json_config_t *cfg,
                               int current_depth, strbuf_t *json, node_value_List* list)
{
    int comma, keytype;

    /* Object */
    strbuf_append_mem(json, "{\n", 2);

    /* table */
    comma = 0;
    // printf("list->length %d\n", list->length);
    for(int i = 0; i < list->length; ++i) {
        if (comma) {
            strbuf_append_mem(json, ",\n", 2);
        }
        else
        {
            comma = 1;
        }
        // 
        strbuf_append_mem(json, charspace, current_depth*2);

        /* table, key */
        keytype = list->list[i].type;
        if (keytype == LUA_TNUMBER) {
            strbuf_append_char(json, '[');
            lua_pushinteger(l, list->list[i].value.i);
            json_append_number(l, cfg, json, -1);
            strbuf_append_mem(json, "]=", 2);

        } else if (keytype == LUA_TSTRING) {
            int add_quoted = 0;
            if (check_key_word(list->list[i].value.s.s, list->list[i].value.s.len))
                add_quoted = 2;
            lua_pushlstring(l, list->list[i].value.s.s, list->list[i].value.s.len);
            json_append_string(l, json, -1, add_quoted);
            strbuf_append_char(json, '=');
        } else {
            printf("error key type %d\n", keytype);
            json_encode_exception(l, cfg, json, -2,
                                  "table key must be a number or string");
            assert(false);
            /* never returns */
        }

        lua_rawget(l, -2);
        /* table, key, value */
        json_append_data(l, cfg, current_depth, json);
        // strbuf_append_char(json, ',');
        // strbuf_append_char(json, '\n');
        lua_pop(l, 1);
        /* table, key */
    }

    strbuf_append_char(json, '\n');
    strbuf_append_mem(json, charspace, (current_depth-1)*2);
    strbuf_append_char(json, '}');
}

static void json_append_object_unordered(lua_State *l, json_config_t *cfg,
                               int current_depth, strbuf_t *json)
{
    int comma, keytype;

    /* Object */
    strbuf_append_mem(json, "{\n", 2);

    /* table */
    comma = 0;
    lua_pushnil(l);
    while (lua_next(l, -2) != 0) {
        if (comma) {
            strbuf_append_mem(json, ",\n", 2);
        }
        else
        {
            comma = 1;
        }
        // 
        strbuf_append_mem(json, charspace, current_depth*2);

        /* table, key, value */
        keytype = lua_type(l, -2);
        if (keytype == LUA_TNUMBER) {
            strbuf_append_char(json, '[');
            json_append_number(l, cfg, json, -2);
            strbuf_append_mem(json, "]=", 2);

        } else if (keytype == LUA_TSTRING) {
            size_t len;
            const char * k = lua_tolstring(l, -2, &len);
            int add_quoted = 0;
            if (check_key_word(k, len))
                add_quoted = 2;
            json_append_string(l, json, -2, add_quoted);
            strbuf_append_char(json, '=');

        } else {
            printf("error key type %d\n", keytype);
            json_encode_exception(l, cfg, json, -2,
                                  "table key must be a number or string");
            /* never returns */
        }

        /* table, key, value */
        json_append_data(l, cfg, current_depth, json);
        // strbuf_append_char(json, ',');
        // strbuf_append_char(json, '\n');
        lua_pop(l, 1);
        /* table, key */
    }

    strbuf_append_char(json, '\n');
    strbuf_append_mem(json, charspace, (current_depth-1)*2);
    strbuf_append_char(json, '}');
}

/* Serialise Lua data into JSON string. */
static void json_append_data(lua_State *l, json_config_t *cfg,
                             int current_depth, strbuf_t *json)
{
    // int len = 0;

    switch (lua_type(l, -1)) {
    case LUA_TSTRING:
        json_append_string(l, json, -1, 1);
        break;
    case LUA_TNUMBER:
        json_append_number(l, cfg, json, -1);
        break;
    case LUA_TBOOLEAN:
        if (lua_toboolean(l, -1))
            strbuf_append_mem(json, "true", 4);
        else
            strbuf_append_mem(json, "false", 5);
        break;
    case LUA_TTABLE:
        current_depth++;
        json_check_encode_depth(l, cfg, current_depth, json);
        // find narr and nres
        Table *p = (Table*)lua_topointer(l, -1);
        //int narr = p->sizearray;
        int narr = p->alimit;
        int nrec = (p->lastfree == NULL)?(0):(sizenode(p));
        // 有数组以外的数据
        if (nrec > 0)
        {
            if (is_order)
            {
                node_value_List list;
                node_value_list_init(&list, narr + nrec);
                sort_keys(l, cfg, json, &list);
                json_append_object(l, cfg, current_depth, json, &list);
                node_value_list_release(&list);
            }
            else
            {
                json_append_object_unordered(l, cfg, current_depth, json);
            }
        }
        else
            json_append_array(l, cfg, current_depth, json, narr);
        break;
    case LUA_TNIL:
        strbuf_append_mem(json, "null", 4);
        break;
    case LUA_TLIGHTUSERDATA:
        if (lua_touserdata(l, -1) == NULL) {
            strbuf_append_mem(json, "null", 4);
            break;
        }
    default:
        /* Remaining types (LUA_TFUNCTION, LUA_TUSERDATA, LUA_TTHREAD,
         * and LUA_TLIGHTUSERDATA) cannot be serialised */
        json_encode_exception(l, cfg, json, -1, "type not supported");
        /* never returns */
    }
}

static int json_encode(lua_State *l)
{
    json_config_t *cfg = json_fetch_config(l);
    strbuf_t local_encode_buf;
    strbuf_t *encode_buf;
    char *json;
    int len;

    luaL_argcheck(l, lua_gettop(l) <= 2, 1, "expected 2 argument");
    if(lua_gettop(l) == 2)
    {
        is_order = lua_toboolean(l, -1);
        lua_pop(l, 1);
    }
    else
        is_order = true;

    if (!cfg->encode_keep_buffer) {
        /* Use private buffer */
        encode_buf = &local_encode_buf;
        strbuf_init(encode_buf, 0);
    } else {
        /* Reuse existing buffer */
        encode_buf = &cfg->encode_buf;
        strbuf_reset(encode_buf);
    }
    //
    strbuf_append_mem(encode_buf, "return ", 7);

    json_append_data(l, cfg, 0, encode_buf);
    json = strbuf_string(encode_buf, &len);

    lua_pushlstring(l, json, len);

    if (!cfg->encode_keep_buffer)
        strbuf_free(encode_buf);

    return 1;
}


/* ===== INITIALISATION ===== */

#if !defined(LUA_VERSION_NUM) || LUA_VERSION_NUM < 502
/* Compatibility for Lua 5.1.
 *
 * luaL_setfuncs() is used to create a module table where the functions have
 * json_config_t as their first upvalue. Code borrowed from Lua 5.2 source. */
static void luaL_setfuncs (lua_State *l, const luaL_Reg *reg, int nup)
{
    int i;

    luaL_checkstack(l, nup, "too many upvalues");
    for (; reg->name != NULL; reg++) {  /* fill the table with given functions */
        for (i = 0; i < nup; i++)  /* copy upvalues to the top */
            lua_pushvalue(l, -nup);
        lua_pushcclosure(l, reg->func, nup);  /* closure with those upvalues */
        lua_setfield(l, -(nup + 2), reg->name);
    }
    lua_pop(l, nup);  /* remove upvalues */
}
#endif


int luaopen_luaserialize(lua_State *l)
{
    luaL_Reg reg[] = {
        { "encode", json_encode },
        { "encode_keep_buffer", json_cfg_encode_keep_buffer },
        // { "encode_sparse_array", json_cfg_encode_sparse_array },
        // { "encode_number_precision", json_cfg_encode_number_precision },
        { NULL, NULL }
    };

    /* Initialise number conversions */
    fpconv_init();

    /* cjson module table */
    lua_newtable(l);

    /* Register functions with config data as upvalue */
    json_create_config(l);
    luaL_setfuncs(l, reg, 1);

    /* Set cjson.null */
    lua_pushlightuserdata(l, NULL);
    lua_setfield(l, -2, "null");

    /* Set module name / version fields */
    lua_pushliteral(l, CJSON_MODNAME);
    lua_setfield(l, -2, "_NAME");
    lua_pushliteral(l, CJSON_VERSION);
    lua_setfield(l, -2, "_VERSION");

    return 1;
}


