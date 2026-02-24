//! Lua 5.4 os library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

thread_local! {
    static PROCESS_START: Instant = Instant::now();
}

/// Register the os library into _ENV.
pub fn register(env_idx: GcIdx<Table>, gc: &mut GcHeap, strings: &mut StringInterner) {
    let os_table = gc.alloc_table(0, 16);

    register_fn(gc, os_table, strings, "clock", native_os_clock);
    register_fn(gc, os_table, strings, "time", native_os_time);
    register_fn(gc, os_table, strings, "difftime", native_os_difftime);
    register_fn(gc, os_table, strings, "date", native_os_date);
    register_fn(gc, os_table, strings, "execute", native_os_execute);
    register_fn(gc, os_table, strings, "getenv", native_os_getenv);
    register_fn(gc, os_table, strings, "remove", native_os_remove);
    register_fn(gc, os_table, strings, "rename", native_os_rename);
    register_fn(gc, os_table, strings, "tmpname", native_os_tmpname);
    register_fn(gc, os_table, strings, "exit", native_os_exit);
    register_fn(gc, os_table, strings, "setlocale", native_os_setlocale);

    let os_name = strings.intern(b"os");
    gc.get_table_mut(env_idx)
        .raw_set_str(os_name, TValue::from_table(os_table));
}

fn register_fn(
    gc: &mut GcHeap,
    table: GcIdx<Table>,
    strings: &mut StringInterner,
    name: &'static str,
    func: fn(&mut NativeContext) -> Result<Vec<TValue>, NativeError>,
) {
    let idx = gc.alloc_native(func, name);
    let val = TValue::from_native(idx);
    let key = strings.intern(name.as_bytes());
    gc.get_table_mut(table).raw_set_str(key, val);
}

// ---------------------------------------------------------------------------
// os.clock()
// ---------------------------------------------------------------------------

fn native_os_clock(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let _ = ctx;
    let elapsed = PROCESS_START.with(|start| start.elapsed());
    let seconds = elapsed.as_secs_f64();
    Ok(vec![TValue::from_float(seconds)])
}

// ---------------------------------------------------------------------------
// os.time([table])
// ---------------------------------------------------------------------------

fn native_os_time(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if arg.is_nil() {
        // Return current time as seconds since epoch
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default();
        let secs = now.as_secs() as i64;
        Ok(vec![TValue::from_full_integer(secs, ctx.gc)])
    } else if let Some(tbl_idx) = arg.as_table_idx() {
        // Construct time from table fields: year, month, day, hour, min, sec
        let year = get_table_int_field(ctx.gc, ctx.strings, tbl_idx, "year")?
            .ok_or_else(|| NativeError::String("field 'year' is missing in date table".into()))?;
        let month = get_table_int_field(ctx.gc, ctx.strings, tbl_idx, "month")?
            .ok_or_else(|| NativeError::String("field 'month' is missing in date table".into()))?;
        let day = get_table_int_field(ctx.gc, ctx.strings, tbl_idx, "day")?
            .ok_or_else(|| NativeError::String("field 'day' is missing in date table".into()))?;
        let hour = get_table_int_field(ctx.gc, ctx.strings, tbl_idx, "hour")?.unwrap_or(12);
        let min = get_table_int_field(ctx.gc, ctx.strings, tbl_idx, "min")?.unwrap_or(0);
        let sec = get_table_int_field(ctx.gc, ctx.strings, tbl_idx, "sec")?.unwrap_or(0);

        // Validate field ranges (matching PUC Lua's struct tm int range checks)
        let check_int_range = |val: i64, name: &str| -> Result<(), NativeError> {
            if val < i32::MIN as i64 || val > i32::MAX as i64 {
                Err(NativeError::String(format!(
                    "field '{}' is out-of-bound",
                    name
                )))
            } else {
                Ok(())
            }
        };
        // year - 1900 must fit in i32 (tm_year)
        let tm_year = year
            .checked_sub(1900)
            .ok_or_else(|| NativeError::String("field 'year' is out-of-bound".to_string()))?;
        check_int_range(tm_year, "year")?;
        // month - 1 must fit in i32 (tm_mon)
        check_int_range(month - 1, "month")?;
        check_int_range(day, "day")?;
        check_int_range(hour, "hour")?;
        check_int_range(min, "min")?;
        check_int_range(sec, "sec")?;

        // Convert to Unix timestamp using a simplified calculation.
        // This handles dates from 1970 onwards correctly.
        let ts = datetime_to_timestamp(year, month, day, hour, min, sec);

        // Normalize the table fields (PUC Lua 5.3.3+)
        let norm = timestamp_to_datetime(ts);
        let set_field = |gc: &mut GcHeap, strings: &mut StringInterner, name: &str, val: i64| {
            let key = strings.intern(name.as_bytes());
            let tval = TValue::from_full_integer(val, gc);
            gc.get_table_mut(tbl_idx).raw_set_str(key, tval);
        };
        set_field(ctx.gc, ctx.strings, "year", norm.year);
        set_field(ctx.gc, ctx.strings, "month", norm.month);
        set_field(ctx.gc, ctx.strings, "day", norm.day);
        set_field(ctx.gc, ctx.strings, "hour", norm.hour);
        set_field(ctx.gc, ctx.strings, "min", norm.min);
        set_field(ctx.gc, ctx.strings, "sec", norm.sec);
        set_field(ctx.gc, ctx.strings, "wday", norm.wday);
        set_field(ctx.gc, ctx.strings, "yday", norm.yday);

        Ok(vec![TValue::from_full_integer(ts, ctx.gc)])
    } else {
        Err(NativeError::String(
            "bad argument #1 to 'time' (table expected)".into(),
        ))
    }
}

/// Read an integer field from a table, returning None if the field is nil.
fn get_table_int_field(
    gc: &GcHeap,
    strings: &mut StringInterner,
    tbl_idx: GcIdx<Table>,
    field: &str,
) -> Result<Option<i64>, NativeError> {
    let key = strings.intern(field.as_bytes());
    let val = gc.get_table(tbl_idx).raw_get_str(key);
    if val.is_nil() {
        return Ok(None);
    }
    if let Some(i) = val.as_full_integer(gc) {
        return Ok(Some(i));
    }
    if let Some(f) = val.as_float() {
        // Only accept float if it's a whole integer value
        if f == (f as i64 as f64) && f.is_finite() {
            return Ok(Some(f as i64));
        }
        return Err(NativeError::String(format!(
            "field '{}' is not an integer",
            field
        )));
    }
    Err(NativeError::String(format!(
        "field '{}' is not an integer",
        field
    )))
}

/// Convert a date/time to a Unix timestamp (seconds since epoch).
/// Simplified calculation, handles dates from 1970+ in UTC.
fn datetime_to_timestamp(year: i64, month: i64, day: i64, hour: i64, min: i64, sec: i64) -> i64 {
    // Adjust for months: if month <= 2, treat as month+12 of previous year
    let (y, m) = if month <= 2 {
        (year - 1, month + 12)
    } else {
        (year, month)
    };

    // Days from epoch to year
    let days = 365 * y + y / 4 - y / 100 + y / 400 + (153 * (m - 3) + 2) / 5 + day - 719469;

    days * 86400 + hour * 3600 + min * 60 + sec
}

// ---------------------------------------------------------------------------
// os.difftime(t2, t1)
// ---------------------------------------------------------------------------

fn native_os_difftime(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let t2 = get_number_arg(ctx, 0, "difftime")?;
    let t1 = get_number_arg(ctx, 1, "difftime")?;
    Ok(vec![TValue::from_float(t2 - t1)])
}

/// Get a numeric arg as f64, coercing integers.
fn get_number_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<f64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(f) = val.as_float() {
        return Ok(f);
    }
    if let Some(i) = val.as_full_integer(ctx.gc) {
        return Ok(i as f64);
    }
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (number expected, got {})",
        idx + 1,
        fname,
        type_name(val)
    )))
}

fn type_name(val: TValue) -> &'static str {
    if val.is_nil() {
        "nil"
    } else if val.is_bool() {
        "boolean"
    } else if val.is_integer() || val.is_float() {
        "number"
    } else if val.is_string() {
        "string"
    } else if val.is_table() {
        "table"
    } else if val.is_function() {
        "function"
    } else {
        "userdata"
    }
}

// ---------------------------------------------------------------------------
// os.date([format [, time]])
// ---------------------------------------------------------------------------

fn native_os_date(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // Get format string (default "%c")
    let fmt_arg = ctx.args.first().copied().unwrap_or(TValue::nil());
    let format_bytes;
    let format_str = if fmt_arg.is_nil() {
        "%c"
    } else if let Some(sid) = fmt_arg.as_string_id() {
        format_bytes = ctx.strings.get_bytes(sid).to_vec();
        std::str::from_utf8(&format_bytes)
            .map_err(|_| NativeError::String("bad argument #1 to 'date' (invalid UTF-8)".into()))?
    } else {
        return Err(NativeError::String(
            "bad argument #1 to 'date' (string expected)".into(),
        ));
    };

    // Get time argument (default: current time)
    let time_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let timestamp = if time_arg.is_nil() {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64
    } else if let Some(i) = time_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = time_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'date' (number expected)".into(),
        ));
    };

    // Decompose timestamp into components
    let dt = timestamp_to_datetime(timestamp);

    // Handle "!" prefix (UTC) -- we always use UTC, so just strip it
    let format_str = format_str.strip_prefix('!').unwrap_or(format_str);

    // Handle "*t" format: return a table
    if format_str == "*t" {
        let tbl = gc_alloc_date_table(ctx.gc, ctx.strings, &dt);
        return Ok(vec![TValue::from_table(tbl)]);
    }

    // Format the date string
    let result = format_date(format_str, &dt).map_err(NativeError::String)?;
    let sid = ctx.strings.intern_or_create(result.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

/// Date/time components (UTC).
struct DateTime {
    year: i64,
    month: i64, // 1-12
    day: i64,   // 1-31
    hour: i64,  // 0-23
    min: i64,   // 0-59
    sec: i64,   // 0-59
    wday: i64,  // 1=Sunday, 2=Monday, ..., 7=Saturday
    yday: i64,  // 1-366
}

/// Convert Unix timestamp to date/time components (UTC).
fn timestamp_to_datetime(ts: i64) -> DateTime {
    let mut remaining = ts;
    let sec = remaining.rem_euclid(60);
    remaining = remaining.div_euclid(60);
    let min = remaining.rem_euclid(60);
    remaining = remaining.div_euclid(60);
    let hour = remaining.rem_euclid(24);
    let mut days = remaining.div_euclid(24);

    // Day of week: Jan 1, 1970 was a Thursday (wday=5 in Lua 1=Sunday)
    let wday = (days.rem_euclid(7) + 5) % 7 + 1; // 1=Sunday

    // Convert days since epoch to year/month/day
    // Algorithm from http://howardhinnant.github.io/date_algorithms.html
    days += 719468; // shift epoch from 1970-01-01 to 0000-03-01
    let era = if days >= 0 { days } else { days - 146096 } / 146097;
    let doe = days - era * 146097; // day of era [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365; // year of era [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // day of year [0, 365]
    let mp = (5 * doy + 2) / 153; // month [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // day [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // month [1, 12]
    let y = if m <= 2 { y + 1 } else { y };

    // Calculate day of year (1-based)
    let yday = day_of_year(y, m, d);

    DateTime {
        year: y,
        month: m,
        day: d,
        hour,
        min,
        sec,
        wday,
        yday,
    }
}

/// Calculate day of year (1-based).
fn day_of_year(year: i64, month: i64, day: i64) -> i64 {
    let is_leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let month_days: [i64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    let mut yday = day;
    for &days in month_days.iter().take((month - 1) as usize) {
        yday += days;
    }
    if is_leap && month > 2 {
        yday += 1;
    }
    yday
}

/// Allocate a table with date/time fields for "*t" format.
fn gc_alloc_date_table(
    gc: &mut GcHeap,
    strings: &mut StringInterner,
    dt: &DateTime,
) -> GcIdx<Table> {
    let tbl = gc.alloc_table(0, 10);

    let set_int = |gc: &mut GcHeap, strings: &mut StringInterner, name: &str, val: i64| {
        let key = strings.intern(name.as_bytes());
        let tval = TValue::from_full_integer(val, gc);
        gc.get_table_mut(tbl).raw_set_str(key, tval);
    };

    set_int(gc, strings, "year", dt.year);
    set_int(gc, strings, "month", dt.month);
    set_int(gc, strings, "day", dt.day);
    set_int(gc, strings, "hour", dt.hour);
    set_int(gc, strings, "min", dt.min);
    set_int(gc, strings, "sec", dt.sec);
    set_int(gc, strings, "wday", dt.wday);
    set_int(gc, strings, "yday", dt.yday);

    let isdst_key = strings.intern(b"isdst");
    gc.get_table_mut(tbl)
        .raw_set_str(isdst_key, TValue::from_bool(false));

    tbl
}

static WEEKDAY_NAMES: [&str; 7] = [
    "Sunday",
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
];
static WEEKDAY_ABBR: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
static MONTH_NAMES: [&str; 12] = [
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
];
static MONTH_ABBR: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
];

/// Format a date string using strftime-like format codes.
fn format_date(fmt: &str, dt: &DateTime) -> Result<String, String> {
    let mut result = String::new();
    let mut chars = fmt.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '%' {
            if let Some(&spec) = chars.peek() {
                chars.next();
                match spec {
                    'Y' => result.push_str(&format!("{:04}", dt.year)),
                    'y' => result.push_str(&format!("{:02}", dt.year % 100)),
                    'm' => result.push_str(&format!("{:02}", dt.month)),
                    'd' => result.push_str(&format!("{:02}", dt.day)),
                    'H' => result.push_str(&format!("{:02}", dt.hour)),
                    'M' => result.push_str(&format!("{:02}", dt.min)),
                    'S' => result.push_str(&format!("{:02}", dt.sec)),
                    'A' => {
                        let idx = (dt.wday - 1) as usize % 7;
                        result.push_str(WEEKDAY_NAMES[idx]);
                    }
                    'a' => {
                        let idx = (dt.wday - 1) as usize % 7;
                        result.push_str(WEEKDAY_ABBR[idx]);
                    }
                    'B' => {
                        let idx = (dt.month - 1) as usize % 12;
                        result.push_str(MONTH_NAMES[idx]);
                    }
                    'b' | 'h' => {
                        let idx = (dt.month - 1) as usize % 12;
                        result.push_str(MONTH_ABBR[idx]);
                    }
                    'c' => {
                        // Default date+time representation
                        let idx_w = (dt.wday - 1) as usize % 7;
                        let idx_m = (dt.month - 1) as usize % 12;
                        result.push_str(&format!(
                            "{} {} {:2} {:02}:{:02}:{:02} {:04}",
                            WEEKDAY_ABBR[idx_w],
                            MONTH_ABBR[idx_m],
                            dt.day,
                            dt.hour,
                            dt.min,
                            dt.sec,
                            dt.year
                        ));
                    }
                    'p' => {
                        if dt.hour < 12 {
                            result.push_str("AM");
                        } else {
                            result.push_str("PM");
                        }
                    }
                    'I' => {
                        let h = if dt.hour == 0 {
                            12
                        } else if dt.hour > 12 {
                            dt.hour - 12
                        } else {
                            dt.hour
                        };
                        result.push_str(&format!("{:02}", h));
                    }
                    'X' => {
                        // Time representation
                        result.push_str(&format!("{:02}:{:02}:{:02}", dt.hour, dt.min, dt.sec));
                    }
                    'x' => {
                        // Date representation
                        result.push_str(&format!(
                            "{:02}/{:02}/{:02}",
                            dt.month,
                            dt.day,
                            dt.year % 100
                        ));
                    }
                    'j' => {
                        result.push_str(&format!("{:03}", dt.yday));
                    }
                    'w' => {
                        // Weekday as number (0=Sunday)
                        result.push_str(&format!("{}", (dt.wday - 1) % 7));
                    }
                    '%' => result.push('%'),
                    'n' => result.push('\n'),
                    't' => result.push('\t'),
                    _ => {
                        return Err(format!("invalid conversion specifier '%{}'", spec));
                    }
                }
            } else {
                return Err("invalid conversion specifier '%'".to_string());
            }
        } else {
            result.push(c);
        }
    }

    Ok(result)
}

// ---------------------------------------------------------------------------
// os.execute([command])
// ---------------------------------------------------------------------------

fn native_os_execute(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if arg.is_nil() {
        // Shell is available
        return Ok(vec![TValue::from_bool(true)]);
    }

    let cmd = if let Some(sid) = arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes).map_err(|_| {
            NativeError::String("bad argument #1 to 'execute' (invalid UTF-8)".into())
        })?
    } else {
        return Err(NativeError::String(
            "bad argument #1 to 'execute' (string expected)".into(),
        ));
    };

    let output = std::process::Command::new("sh")
        .arg("-c")
        .arg(&cmd)
        .output();

    match output {
        Ok(out) => {
            let code = out.status.code().unwrap_or(-1);
            let exit_type = ctx.strings.intern(b"exit");
            if out.status.success() {
                Ok(vec![
                    TValue::from_bool(true),
                    TValue::from_string_id(exit_type),
                    TValue::from_full_integer(code as i64, ctx.gc),
                ])
            } else {
                Ok(vec![
                    TValue::nil(),
                    TValue::from_string_id(exit_type),
                    TValue::from_full_integer(code as i64, ctx.gc),
                ])
            }
        }
        Err(e) => Err(NativeError::String(format!(
            "os.execute: failed to execute command: {}",
            e
        ))),
    }
}

// ---------------------------------------------------------------------------
// os.getenv(varname)
// ---------------------------------------------------------------------------

fn native_os_getenv(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());
    let varname = if let Some(sid) = arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes).map_err(|_| {
            NativeError::String("bad argument #1 to 'getenv' (invalid UTF-8)".into())
        })?
    } else {
        return Err(NativeError::String(
            "bad argument #1 to 'getenv' (string expected)".into(),
        ));
    };

    match std::env::var(&varname) {
        Ok(val) => {
            let sid = ctx.strings.intern_or_create(val.as_bytes());
            Ok(vec![TValue::from_string_id(sid)])
        }
        Err(_) => Ok(vec![TValue::nil()]),
    }
}

// ---------------------------------------------------------------------------
// os.remove(filename)
// ---------------------------------------------------------------------------

fn native_os_remove(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());
    let filename = if let Some(sid) = arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes).map_err(|_| {
            NativeError::String("bad argument #1 to 'remove' (invalid UTF-8)".into())
        })?
    } else {
        return Err(NativeError::String(
            "bad argument #1 to 'remove' (string expected)".into(),
        ));
    };

    match std::fs::remove_file(&filename) {
        Ok(()) => Ok(vec![TValue::from_bool(true)]),
        Err(e) => {
            let msg = format!("{}: {}", filename, e);
            let sid = ctx.strings.intern_or_create(msg.as_bytes());
            Ok(vec![TValue::nil(), TValue::from_string_id(sid)])
        }
    }
}

// ---------------------------------------------------------------------------
// os.rename(oldname, newname)
// ---------------------------------------------------------------------------

fn native_os_rename(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let old_arg = ctx.args.first().copied().unwrap_or(TValue::nil());
    let new_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());

    let oldname = if let Some(sid) = old_arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes).map_err(|_| {
            NativeError::String("bad argument #1 to 'rename' (invalid UTF-8)".into())
        })?
    } else {
        return Err(NativeError::String(
            "bad argument #1 to 'rename' (string expected)".into(),
        ));
    };

    let newname = if let Some(sid) = new_arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes).map_err(|_| {
            NativeError::String("bad argument #2 to 'rename' (invalid UTF-8)".into())
        })?
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'rename' (string expected)".into(),
        ));
    };

    match std::fs::rename(&oldname, &newname) {
        Ok(()) => Ok(vec![TValue::from_bool(true)]),
        Err(e) => {
            let msg = format!("{}: {}", oldname, e);
            let sid = ctx.strings.intern_or_create(msg.as_bytes());
            Ok(vec![TValue::nil(), TValue::from_string_id(sid)])
        }
    }
}

// ---------------------------------------------------------------------------
// os.tmpname()
// ---------------------------------------------------------------------------

fn native_os_tmpname(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // Generate a unique temp file name using process id and a counter
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);

    let pid = std::process::id();
    let cnt = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format!("/tmp/lua_tmpname_{}_{}", pid, cnt);
    let sid = ctx.strings.intern_or_create(name.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

// ---------------------------------------------------------------------------
// os.exit([code [, close]])
// ---------------------------------------------------------------------------

fn native_os_exit(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let code = if let Some(val) = ctx.args.first().copied() {
        if val.is_nil() {
            0
        } else if let Some(b) = val.as_bool() {
            if b {
                0
            } else {
                1
            }
        } else if let Some(i) = val.as_full_integer(ctx.gc) {
            i as i32
        } else if let Some(f) = val.as_float() {
            f as i32
        } else {
            0
        }
    } else {
        0
    };

    std::process::exit(code);
}

// ---------------------------------------------------------------------------
// os.setlocale(locale [, category])
// ---------------------------------------------------------------------------

fn native_os_setlocale(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // Stub: we only support the "C" locale.
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if arg.is_nil() {
        // Query current locale: return "C"
        let sid = ctx.strings.intern(b"C");
        return Ok(vec![TValue::from_string_id(sid)]);
    }

    if let Some(sid) = arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        let locale = std::str::from_utf8(&bytes).unwrap_or("");
        if locale == "C" || locale.is_empty() || locale == "POSIX" {
            let result_sid = ctx.strings.intern(b"C");
            return Ok(vec![TValue::from_string_id(result_sid)]);
        }
        // Unsupported locale
        return Ok(vec![TValue::nil()]);
    }

    Err(NativeError::String(
        "bad argument #1 to 'setlocale' (string expected)".into(),
    ))
}
