pub mod snake;
pub mod progress_bar;
pub mod spinner;
mod smargs;

// Re-exports the struct to be directly used from `terminal_toys`
pub use progress_bar::ProgressBar;
pub use smargs::{Smargs, List, Smarg, SmargKind, Break as SmargsBreak, SmargsResult, Error as SmargsError};


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

/// Convenience-macro for describing your program and its expected arguments,
/// constructing a `Smargs` instance and then parsing the actual arguments.
///
/// # Examples:
/// Program description and arguments are defined using a list of tuples
/// `(description, keys, kind)` and finally parsed from an `Iterator<Item =
/// String>` into requested types:
/// ```
/// struct Input(usize, bool, String);
/// let Input(foo, bar, baz) = terminal_toys::smargs!(
///     "An example",
///     Input(
///         ("Foo", [], terminal_toys::SmargKind::Optional("42")),
///         ("Bar", ["b"], terminal_toys::SmargKind::Flag),
///         ("Baz", ["z", "baz"], terminal_toys::SmargKind::Required),
///     ),
/// )
/// .parse(vec!["x", "Bazbaz"].into_iter().map(String::from))
/// .unwrap();
/// 
/// assert_eq!(foo, 42_usize);
/// assert_eq!(bar, false);
/// assert_eq!(baz, "Bazbaz".to_owned());
/// ```
/// Structs with named fields are also supported:
/// ```
/// # fn main() -> Result<(), String> {
/// use terminal_toys::{smargs, List, SmargKind as Sk};
///
/// struct RegistrationInfo {
///     names: List<String>,
///     age: usize,
///     domain: String,
///     no_news: bool,
/// }
/// 
/// let args = vec![
///    "register",
///    "--no-newsletter",
///    "-a", "26",
///    "-d", "hatch",
///    "Matt", "-n", "Myman", "-n", "Jr"
/// ];
/// 
/// let RegistrationInfo { names, age, domain, no_news } = smargs!(
///     "Register for service",
///     RegistrationInfo {
///         no_news:("Opt-out from receiving newsletter",     ["no-newsletter"], Sk::Flag),
///         names:  ("All portions of your full name listed", ["n"],             Sk::List(1)),
///         domain: ("Email address domain",                  ["d"],             Sk::Optional("getspam")),
///         age:    ("Your age",                              ["a", "age"],      Sk::Required)
///     },
/// )
/// .parse(args.into_iter().map(String::from))
/// .map_err(|e| e.to_string())?;
/// 
/// let mut newsletter_subscribers = vec![];
///
/// if age < 18 {
///     let ys = 18 - age;
///     let putdown = format!(
///         "come back in {}",
///          if ys == 1 { "a year".to_owned() } else { format!("{} years", ys) }
///     );
///     eprintln!("Failed to register: {}", putdown);
///     std::process::exit(1);
/// }
///
/// let user_email = format!("{}.{}@{}.com", names.0.join("."), age, domain).replace(' ', ".").to_lowercase();
///
/// let subscriber_count = newsletter_subscribers.len();
/// if !no_news {
///     newsletter_subscribers.push(&user_email);
/// }
///
/// assert_eq!(user_email, "matt.myman.jr.26@hatch.com".to_string());
/// assert_eq!(newsletter_subscribers.len(), subscriber_count);
/// # Ok(()) }
/// ```
/// Required arguments can be parsed based on the order in the macro's
/// definition-list. Missing, but optional, arguments use the given default
/// value.
/// ```
/// # fn main() -> Result<(), String> {
/// use terminal_toys::{smargs, List, SmargKind as Sk};
///
/// struct RegistrationInfo {
///     names: List<String>,
///     age: usize,
///     domain: String,
///     no_news: bool,
/// }
/// 
/// let args = vec!["register.exe", "Matt Myman", "26"];
/// 
/// let RegistrationInfo { names, age, domain, no_news } = smargs!(
///     "Register for service",
///     RegistrationInfo {
///         no_news:("Opt-out from receiving newsletter",     ["no-newsletter"], Sk::Flag),
///         names:  ("All portions of your full name listed", ["n"],             Sk::List(1)),
///         domain: ("Email address domain",                  ["d"],             Sk::Optional("getspam")),
///         age:    ("Your age",                              ["a", "age"],      Sk::Required)
///     },
/// )
/// .parse(args.into_iter().map(String::from))
/// .map_err(|e| e.to_string())?;
/// 
/// assert!(!no_news);
/// assert_eq!(names.0, vec!["Matt Myman"]);
/// assert_eq!(domain, "getspam".to_string());
/// assert_eq!(age, 26);
/// # Ok(()) }
/// ```
#[macro_export]
macro_rules! smargs {
    ( $program_desc:literal , $container_name:ident $container:tt $(,)? ) => {
        {
            use terminal_toys::{container_parse, unwrap_parse, container_push, unwrap_push, Smargs, Smarg, SmargKind, SmargsError};
            // Implement parsing into the given __custom__ (needed for passing
            // it to Smargs<Ts>) output type (with special Result-type when so
            // requested, because of the orphan rule/possibility of "upstream
            // changes").
            impl std::convert::TryFrom<Smargs<$container_name>> for $container_name {
                type Error = SmargsError;
                fn try_from(mut smargs: Smargs<Self>) -> Result<Self, Self::Error> {
                    Ok(
                        container_parse!( smargs, $container_name $container )
                    )
                }
            }

            let mut smargs = Smargs::<$container_name>::new($program_desc);
            container_push!( smargs, $container );

            smargs
        }
    };
}

/// Simply create the line for unwrapping the next value in `smargs`. Needed just for
/// repeating the amount of values required.
#[macro_export]
macro_rules! unwrap_parse {
    ( $smargs:expr, $_kind:expr ) => {
        $smargs.parse_next()?
    };
}

#[macro_export]
macro_rules! unwrap_push {
    ( $smargs:expr, $arg_desc:literal, $keys:expr, $kind:expr ) => {
        $smargs.push(Smarg { desc: $arg_desc, keys: $keys.to_vec(), kind: $kind });
    };
}

#[macro_export]
macro_rules! container_parse {
    // Tuple-struct.
    [ $smargs:expr, $name:ident ( $( ($arg_desc:literal, $keys:expr, $kind:expr $(,)?) ),+ $(,)? ) ] => {
        $name ( $( unwrap_parse!( $smargs, $kind ) ),+ )
    };
    // Named fields.
    [ $smargs:expr, $name:ident { $( $field:ident :($arg_desc:literal, $keys:expr, $kind:expr $(,)?) ),+ $(,)? } ] => {
        $name { $( $field: unwrap_parse!( $smargs, $kind ) ),+ }
    };
}

#[macro_export]
macro_rules! container_push {
    // Tuple-struct.
    [ $smargs:expr, ( $( ($arg_desc:literal, $keys:expr, $kind:expr $(,)?) ),+ $(,)? ) ] => {
        $( unwrap_push!( $smargs, $arg_desc, $keys, $kind ) );+
    };
    // Named fields.
    [ $smargs:expr, { $( $field:ident :($arg_desc:literal, $keys:expr, $kind:expr $(,)?) ),+ $(,)? } ] => {
        $( unwrap_push!( $smargs, $arg_desc, $keys, $kind ) );+
    };
}