pub mod snake;
pub mod progress_bar;
pub mod spinner;
mod smargs;

// Re-exports the struct to be directly used from `terminal_toys`
pub use progress_bar::ProgressBar;
pub use smargs::{Smargs, Smarg, SmargKind, Error as SmargsError};

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;

#[derive(Debug)]
pub enum Color {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
    Gray,
    BrightRed,
    BrightGreen,
    BrightYellow,
    BrightBlue,
    BrightMagenta,
    BrightCyan,
    BrightWhite,
}

impl Color {
    /// Return the color's ANSI-code -string for printing.
    pub fn code(&self) -> &'static str {
        match self {
            Color::Black         => "30",
            Color::Red           => "31",
            Color::Green         => "32",
            Color::Yellow        => "33",
            Color::Blue          => "34",
            Color::Magenta       => "35",
            Color::Cyan          => "36",
            Color::White         => "37",
            Color::Gray          => "90",
            Color::BrightRed     => "91",
            Color::BrightGreen   => "92",
            Color::BrightYellow  => "93",
            Color::BrightBlue    => "94",
            Color::BrightMagenta => "95",
            Color::BrightCyan    => "96",
            Color::BrightWhite   => "97",
        }
    }

    /// Wraps the string in ANSI-code of the specified color for printing.
    ///
    /// # Example
    /// ```
    /// use terminal_toys::Color;
    /// // Print the finnish flag
    /// let blue  = Color::color_string(Color::BrightBlue,  "###");
    /// let white = Color::color_string(Color::BrightWhite, "###");
    /// println!("{}{}{}{}", white, blue,  white, white);
    /// println!("{}{}{}{}", blue,  blue,  blue,  blue );
    /// println!("{}{}{}{}", white, blue,  white, white);
    /// ```
    pub fn color_string(c: Self, s: &str) -> String {
        format!("\x1B[{}m{}\x1B[m", c.code(), s)
    }
}

/// Using `std::print!` wraps the string-formatting in ANSI-code of the
/// specified color.
/// NOTE Printing other ANSI-coloring-codes with this macro will break the
/// specified color from that point for the rest of the print.
/// (Reference used: https://en.wikipedia.org/wiki/ANSI_escape_code#Colors)
///
/// # Example
/// ```
/// use terminal_toys::{Color, color_print};
/// color_print!(Color::Red, "{} - Bad request: {}", 400, "foo",);
/// match Some(42) { Some(n) => color_print!(Color::Green, "OK"), _ => { } }
/// ```
#[macro_export]
macro_rules! color_print {
    // A Color and a string are mandatory arguments;
    // latter starts a sequence that should work like the normal print macro.
    // The third match is for allowing optional trailing comma.
    ($c:expr, $($x:expr),+ $(,)?) => {
        {
            // TODO should line-wrapping be considered?
            // See
            // https://tldp.org/HOWTO/Bash-Prompt-HOWTO/nonprintingchars.html
            // Start the color
            print!("\x1B[{}m", $c.code());
            // Print normally
            print!($($x),+);
            // Reset the color back to normal
            print!("\x1B[m");
        }
    };
}

/// Same as `terminal_toys::color_print` but appends a newline at the end.
/// # Example
/// ```
/// use terminal_toys::{color_println, Color};
/// color_println!(Color::Red, "{} - Bad request: {}", 400, "foo",);
/// match Some(42) { Some(n) => color_println!(Color::Green, "OK"), _ => { } }
/// ```
#[macro_export]
macro_rules! color_println {
    // The third match is for allowing optional trailing comma.
    ($c:expr, $($x:expr),+ $(,)?) => {
        {
            terminal_toys::color_print!($c, $($x),+);
            println!();
        }
    };
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
/// use terminal_toys::{Color, color_log};
/// const TTOYSLOG_COLOR: Color = Color::Yellow;
/// color_log!("Did a {} with {}", "thing", "stuff",);
/// match Some(42) { Some(n) => color_log!("OK"), _ => color_log!("fail") }
/// ```
#[macro_export]
macro_rules! color_log {
    ($($message:expr),+ $(,)?) => {
        if let Some(value) = option_env!("TTOYSLOG") {
            let full_path = module_path!();
            if full_path.split("::").any(|m| value.contains(m)) {
                terminal_toys::color_print!(
                    TTOYSLOG_COLOR, "[{}:{}] ", full_path, line!()
                );
                // Print message with its formatting
                terminal_toys::color_println!(TTOYSLOG_COLOR, $($message),+);
            }
        }
    };
}


/// Convenience-macro for describing your program and its arguments and
/// constructing a `Smargs` instance.
#[macro_export]
macro_rules! smargs {
    ( 
        $program_desc:literal, $( 
            (
                $arg_desc:literal
                , $keys:expr
                , $type_:ty
                $(, $default:expr)?
            )
        ),+
    ) => {
        {
            use std::any;
            use terminal_toys::{Smargs, Smarg, SmargKind};
            let mut smargs = Smargs::<( $( $type_, )+ )>::new($program_desc);
            $(
                {
                    let keys = $keys;
                    let mut default = Option::<&'static str>::None;
                    let mut kind = None;
                    
                    let arg_is_bool = any::TypeId::of::<$type_>() == any::TypeId::of::<bool>();

                    $(
                        // Prevent using default on a bool entirely (Note that
                        // this is a runtime check).
                        if arg_is_bool {
                            panic!("boolean argument defaults only to \"false\" and must do so automatically (remove \"{}\").", $default);
                        }
                        default = Some($default);
                    )?

                    // Select kind based on passed type.
                    kind = Some(
                        if arg_is_bool {
                            // Booleans default to false in any case.
                            SmargKind::Flag
                        } else if let Some(value) = default {
                            let default = value.to_owned();
                            // TODO Check that default is of type type_ e.g. by
                            // trying to parse it here?
                            SmargKind::Optional(value)
                        } else {
                            SmargKind::Required
                        }
                    );

                    let kind = kind.expect("argument definition missing the type or default value");

                    smargs.push(Smarg { desc: $arg_desc, kind, keys });
                }
            )+
            smargs
        }
    };
}
