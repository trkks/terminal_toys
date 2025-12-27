pub mod snake;
pub mod progress_bar;
pub mod spinner;
pub mod smargs;

// Re-exports the struct to be directly used from `terminal_toys`
pub use progress_bar::ProgressBar;


#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;

/// String sequences that when printed start coloring the following text. Note
/// that to stop the coloring (i.e., return back to "normal), append whatever
/// you're coloring with `textcolor::RESET`.
///
/// Reference used: https://en.wikipedia.org/wiki/ANSI_escape_code#Colors
/// 
/// # Examples
/// Highlight errors and successes.
/// ```
/// # use terminal_toys::textcolor::{RED, GREEN, RESET};
/// println!("{}{} - Bad request: {}{}", RED, 400, RESET, "foo",);
/// match Some(42) { Some(n) => println!("{}OK", GREEN), _ => { } }
/// ```
/// Print a 8x7 heart ❤️.
/// ```
/// # use terminal_toys::textcolor::{BLACK, RED, RESET};
/// println!("  {}████{}    {}████{}",       BLACK, RESET, BLACK, RESET);
/// println!("{}██{}████{}████{}████{}██{}", BLACK,   RED, BLACK,   RED, BLACK, RESET);
/// println!("{}██{}████████████{}██{}",     BLACK,   RED, BLACK, RESET);
/// println!("{}██{}████████████{}██{}",     BLACK,   RED, BLACK, RESET);
/// println!("  {}██{}████████{}██{}",       BLACK,   RED, BLACK, RESET);
/// println!("    {}██{}████{}██{}",         BLACK,   RED, BLACK, RESET);
/// println!("      {}████{}",               BLACK, RESET);
/// ```
pub mod textcolor {
    pub const RESET: &str          = "\x1B[m";
    pub const BLACK: &str          = "\x1B[30m";
    pub const RED: &str            = "\x1B[31m";
    pub const GREEN: &str          = "\x1B[32m";
    pub const YELLOW: &str         = "\x1B[33m";
    pub const BLUE: &str           = "\x1B[34m";
    pub const MAGENTA: &str        = "\x1B[35m";
    pub const CYAN: &str           = "\x1B[36m";
    pub const WHITE: &str          = "\x1B[37m";
    pub const GRAY: &str           = "\x1B[90m";
    pub const BRIGHT_RED: &str     = "\x1B[91m";
    pub const BRIGHT_GREEN: &str   = "\x1B[92m";
    pub const BRIGHT_YELLOW: &str  = "\x1B[93m";
    pub const BRIGHT_BLUE: &str    = "\x1B[94m";
    pub const BRIGHT_MAGENTA: &str = "\x1B[95m";
    pub const BRIGHT_CYAN: &str    = "\x1B[96m";
    pub const BRIGHT_WHITE: &str   = "\x1B[97m";
}

/// Log a message from module `x` IF an environment variable `TTOYSLOG` has
/// been set to a module path containing the name of module `x`.
///
/// # Examples of modules to be logged from and their names
/// - `TTOYSLOG=bar` -> log's from module `foo::bar`
/// - `TTOYSLOG=foo` -> log's from modules `foo`, `foo::bar`, `foo::bar::baz`
///
/// # Example
/// ```
/// use terminal_toys::log;
/// log!("Did a {} with {}", "thing", "stuff",);
/// match Some(42) { Some(n) => log!("OK"), _ => log!("fail") }
/// ```
#[macro_export]
macro_rules! log {
    ($($message:expr),+ $(,)?) => {
        if let Some(value) = option_env!("TTOYSLOG") {
            let full_path = module_path!();
            if full_path.split("::").any(|m| value.contains(m)) {
                print!("[{}:{}] ", full_path, line!());
                // Print message with its formatting.
                println!($($message),+);
            }
        }
    };
}

/// Same as the `log`-macro, but color the output according to color variable
/// `TTOYSLOG_COLOR` found in scope.
///
/// NOTE The module to log from is required to contain a constant named
/// `TTOYSLOG_COLOR` and type `Color`!
///
/// # Example:
/// ```
/// // Logs printing out in red.
/// use terminal_toys::{color_log, textcolor};
/// const TTOYSLOG_COLOR: &str = textcolor::YELLOW;
/// color_log!("Did a {} with {}", "thing", "stuff",);
/// match Some(42) { Some(n) => color_log!("OK"), _ => color_log!("fail") }
/// ```
#[macro_export]
macro_rules! color_log {
    ($($message:expr),+ $(,)?) => {
        if let Some(value) = option_env!("TTOYSLOG") {
            let full_path = module_path!();
            if full_path.split("::").any(|m| value.contains(m)) {
                print!("{}[{}:{}] ", TTOYSLOG_COLOR, full_path, line!());
                // Print message with its formatting
                print!("{}", TTOYSLOG_COLOR);
                println!($($message),+);
            }
        }
    };
}

