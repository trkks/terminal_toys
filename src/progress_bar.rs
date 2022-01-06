use std::io::{self, Write, Stdout, Result as IOResult};
use std::iter;

/// An ascii-graphics bar to easily print out the amount of progress a program
/// has done per iteration of a loop or between some other equal sized tasks.
///
/// # Example:
/// ```
/// let mut progress = terminal_toys::ProgressBar::new(1000, 15);
/// progress.title("Amount of work done");
/// for _ in 0..1000 {
///     // -- do work --
///
///     progress.print_update();
///     // Example of output when looped 400 to 499 times:
///     // Amount of work done: [====......]
/// }
/// ```
pub struct ProgressBar {
    source_progress: usize,
    threshold: usize,
    bar: Vec<u8>,
    title: String,
    row: usize,
    prefix: Vec<u8>,
    suffix: Vec<u8>,
    out: Stdout,
}
impl ProgressBar {
    /// Creates a new ProgressBar of `bar_len` characters wide that fills up
    /// based on update count relative to `source_len`
    pub fn new(source_len: usize, bar_len: usize) -> Self {
        // A bar's length is the length of content not '\r', '[' or ']'
        let bar: Vec<u8> = iter::repeat('.' as u8).take(bar_len).collect();
        let title = String::from("Progress");
        let row = 0;
        let prefix = Self::prefix_from(row, &title);

        ProgressBar {
            source_progress: 0,
            threshold: source_len / bar_len,
            bar,
            title,
            row,
            prefix,
            suffix: Self::suffix_from(row),
            out: io::stdout(),
        }
    }

    /// Signal that progress has been made. If this update leads to filling up
    /// the bar, it is printed to stdout for reflecting this new state
    /// Note that the environment must follow some ANSI escape sequences (see
    /// https://tldp.org/HOWTO/Bash-Prompt-HOWTO/x361.html).
    pub fn print_update(&mut self) -> IOResult<()> {
        if self.update() {
            self.print()?
        }
        Ok(())
    }

    /// Change the title shown next to the progress bar
    pub fn title(&mut self, title: &str) {
        self.title = String::from(title);
        // Cache the new prefix now that title has changed
        self.prefix = Self::prefix_from(self.row, &self.title);
    }

    /// Change the row-offset of the progress bar
    pub fn row(&mut self, row: usize) {
        self.row = row;
        // Cache the new prefix and suffix now that row-offset has changed
        self.prefix = Self::prefix_from(self.row, &self.title);
        self.suffix = Self::suffix_from(self.row);
    }

    fn update(&mut self) -> bool {
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

    /// Print based on terminal row on which to position the bar.
    fn print(&mut self) -> IOResult<()> {
        // Flag to choose the right ending based on the bar being full or not
        let bar_progress = self.bar.iter()
            .rposition(|x| *x == '=' as u8)
            .unwrap_or(0) + 1;
        let bar_full = self.bar.len() <= bar_progress;

        // Create a fitting vec for the bytes to be written
        let mut bytes = Vec::with_capacity(
            // bar         + prefix            +"] Done!"
            self.bar.len() + self.prefix.len() + 7
        );

        // Add the correct bytes in order:
        bytes.extend(&self.prefix);

        bytes.extend(self.bar.as_slice());
        if bar_full {
            bytes.extend(b"] Done!");
        } else {
            bytes.extend(b"]")
        }

        bytes.extend(&self.suffix);

        // Write into stdout
        // NOTE Stdout needs to be locked for the write operations
        let mut handle = self.out.lock();
        handle.write(bytes.as_slice())?;
        handle.flush()
    }

    /// Create a string that will move the cursor down the amount of rows
    fn prefix_from(row: usize, title: &str) -> Vec<u8> {
                        // 'B' => Move down n lines
        Vec::from(format!("\x1b[{}B\r{} [", row, title).as_bytes())
    }

    fn suffix_from(row: usize) -> Vec<u8> {
        // Move back up ('A') to the row where started
        Vec::from(format!("\x1b[{}A", row).as_bytes())
    }
}
