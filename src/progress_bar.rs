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
            row: 0,
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
    }

    /// Change the row-offset of the progress bar
    pub fn row(&mut self, row: usize) {
        self.row = row;
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
        // Set how much the cursor will be moved with escape sequences
        let move_rows = format!("\x1b[{}", self.row);
        // Do a little dance, make a little love
        let prefix = {
            let mut temp = Vec::from(move_rows.as_bytes());
            // 'B' => Move down n lines
            temp.extend(b"B\r");
            temp.extend(self.title.as_bytes());
            temp.extend(b" [");
            temp
        };

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

        // Move back up ('A') to the row where started
        bytes.extend(format!("{}A", move_rows).as_bytes());

        // Write into stdout
        // NOTE Stdout needs to be locked for the write operations
        let mut handle = self.out.lock();
        handle.write(bytes.as_slice())?;
        handle.flush()
    }
}
