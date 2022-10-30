pub mod snake;
pub mod progress_bar;
pub mod spinner;
pub mod smargs;

// Re-exports the struct to be directly used from `terminal_toys`
pub use progress_bar::ProgressBar;
pub use smargs::{Smargs, ArgType};


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
/// // Color the output red and format it like with `std::print`
/// color_print!(
///     Color::Red,
///     "Hey {:A>6}, why the long {}?",
///     "Alice",
///     if 1 < 2 { "face" } else { "phase" },
/// );
///
/// color_print!(Color::Green, "foo");
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
/// use terminal_toys::{Color, color_println};
/// color_println!(
///     Color::BrightRed,
///     "Printing in {}",
///     "RED",
/// );
///
/// let opt = Some("foo");
/// match opt {
///     Some(s) => color_println!(Color::Green, "{}", s),
///     None    => color_println!(Color::Red, "Not found"),
/// }
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
/// been set to contain a name associated with path of the module `x`.
///
/// # Examples of modules to be logged from and their names
/// - `crate::foo::bar    => bar`
/// - `crate::baz::qux::* => baz`
///
/// # Example
/// ```
/// terminal_toys::log!("Index {}", "Value");
/// terminal_toys::log!(
///     "{:05} {:>5}\n{:05} {:>5?}",
///     42, true,
///     64, "fail",
/// );
/// ```
#[macro_export]
macro_rules! log {
    ($($message:expr),+ $(,)?) => {
        {
            if let Some(value) = option_env!("TTOYSLOG") {
                if module_path!().split("::").any(|m| value.contains(m)) {
                    // Print message with its formatting
                    println!($($message),+);
                }
            }
        }
    };
}

/// Same as the `log`-macro, but color the output according to color variable
/// `TTOYSLOG_COLOR` found in scope.
///
/// NOTE The module to log from is required to contain a constant `Color` in
/// the form `TTOYSLOG_COLOR`!
///
/// # Example:
/// ```
/// use terminal_toys::{Color, color_log};
/// const TTOYSLOG_COLOR: Color = Color::Red;
/// terminal_toys::color_log!("Index {}", "Value");
/// terminal_toys::color_log!(
///     "{:05} {:>5}\n{:05} {:>5?}",
///     42, true,
///     64, "fail",
/// );
/// ```
#[macro_export]
macro_rules! color_log {
    ($($message:expr),+ $(,)?) => {
        if let Some(value) = option_env!("TTOYSLOG") {
            if module_path!().split("::").any(|m| value.contains(m)) {
                // Print message with its formatting
                terminal_toys::color_println!(TTOYSLOG_COLOR, $($message),+);
            }
        }
    };
}
