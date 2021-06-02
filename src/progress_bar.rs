use std::io::{self, Write, Stdout, Result as IOResult};
use std::iter;

/// An ascii-graphics bar to easily print out the amount of progress a program
/// has done per iteration of a loop or between some other equal sized tasks.
///
/// # Example:
/// ```
/// let mut progress = ProgressBar::new(1000, 15);
/// progress.set_title("Amount of work done");
/// for _ in range(0..1000) {
///     // -- do work --
///
///     progress.print_update()?;
///     // Example of output when looped 400 to 499 times:
///     // Amount of work done: [====......]
/// }
/// ```
pub struct ProgressBar {
    source_progress: usize,
    threshold: usize,
    bar: Vec<u8>,
    title: String,
    out: Stdout,
}
impl ProgressBar {
    /// Creates a new ProgressBar of `bar_len` characters wide that fills up
    /// based on update count relative to `source_len`
    pub fn new(source_len: usize, bar_len: usize) -> Self {
        // A bar's length is the length of content not '\r', '[' or ']'
        let bar : Vec<u8> = iter::repeat('.' as u8)
            .take(bar_len)
            .collect();
        ProgressBar {
            source_progress: 0,
            threshold: source_len / bar_len,
            bar,
            title: String::from("Progress"),
            out: io::stdout(),
        }
    }

    /// Signal that progress has been made. If this update leads to filling up
    /// the bar, it is printed to stdout for reflecting this new state
    pub fn print_update(&mut self) -> IOResult<()> {
        if self.update() {
            self.print(None)?
        }
        Ok(())
    }

    /// Same as `print_update` but specify the terminal row to which position
    /// the bar.
    /// Note that the environment must follow some ANSI escape sequences (see 
    /// https://tldp.org/HOWTO/Bash-Prompt-HOWTO/x361.html).
    pub fn print_update_row(&mut self, row: usize) -> IOResult<()> {
        if self.update() {
            self.print(Some(row))?
        }
        Ok(())
    }


    /// Change the title shown next to the progress bar
    pub fn title(&mut self, title: &str) {
        self.title = String::from(title);
    }

    fn update(&mut self) -> bool{
        // Source has implied a state update, so increment progress
        self.source_progress += 1;
        if self.source_progress % self.threshold == 0 {
            let index = self.bar.iter()
                .position(|x| *x == '.' as u8)
                .unwrap_or(0);
            self.bar[index] = '=' as u8;
            return true
        }
        return false
    }

    fn print(&mut self, row: Option<usize>) -> IOResult<()> {
        // Choose current prefix based on if cursor should be moved to a row
        let prefix = match row {
            Some(r) => format!("\x1b[{};0f\r{} [", r, self.title),
            None    => format!("\r{} [", self.title),
        };
        let prefix = prefix.as_bytes();

        // Flag to choose the right suffix based on the bar being full or not
        let bar_progress = self.bar.iter()
            .rposition(|x| *x == '=' as u8)
            .unwrap_or(0) + 1;
        let bar_full = self.bar.len() <= bar_progress;

        // Create a vec for the bytes to be written
        let mut bytes = vec![];
                   // bar            + prefix       +"] Done!"
        bytes.reserve(self.bar.len() + prefix.len() + 7);

        // Add the correct bytes in order
        bytes.extend(prefix);
        bytes.extend(self.bar.as_slice());
        if bar_full {
            bytes.extend(b"] Done!");
        } else {
            bytes.extend(b"]")
        }

        // Write into stdout
        // NOTE Stdout needs to be locked for the write operations
        let mut handle = self.out.lock();
        handle.write(bytes.as_slice())?;
        handle.flush()
    }
}
