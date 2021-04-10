use std::io::{self, Write, Stdout, Result as IOResult};
use std::sync::mpsc;
use std::time::Duration;
use std::{thread, iter};

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
        let bar : Vec<u8> = iter::repeat('.' as u8).take(bar_len)
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
    /// Note that the environment must follow some old-ass ANSI escape
    /// sequences (see https://tldp.org/HOWTO/Bash-Prompt-HOWTO/x361.html).
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
            let index = self.bar.iter().position(|x| *x == '.' as u8)
                        .unwrap_or(0);
            self.bar[index] = '=' as u8;
            return true
        }
        return false
    }

    fn print(&mut self, row: Option<usize>) -> IOResult<()> {
        let prefix = match row {
            // FIXME The print breaks when the stdout buffer flushes on its own
            // for example, try with multiple threads or with a long width
            Some(r) => format!("\x1b[{};0f\r{} [", r, self.title),
            None    => format!("\r{} [", self.title),
        };

        self.out.write(prefix.as_bytes()).map(|_| ())?;
        self.out.write(self.bar.as_slice()).map(|_| ())?;
        let progressed = self.bar.iter().rposition(|x| *x == '=' as u8)
                                        .unwrap_or(0) + 1;
        if progressed < self.bar.len() {
            self.out.write(b"]").map(|_| ())?;
        } else {
            self.out.write(b"] Done!").map(|_| ())?;
        }
        self.out.flush()
    }
}

/// Starts a spinner animation at the current terminal print position
/// that runs until the end of `concrete_job`, showing that it is processing
pub fn start_spinner<T>(concrete_job: Box<dyn FnOnce() -> T>) -> T {
    // Start the concrete job and in another thread, run the spinner
    // When concrete job finishes, call join on the spinner-thread

    let (sender, receiver) = mpsc::channel();

    // Start the spinner in another thread
    let spinner_job = thread::spawn(move || {

        let sequences = 
            [b"\x1b[3D(|)",b"\x1b[3D(/)",b"\x1b[3D(-)",b"\x1b[3D(\\)"];

        let mut i = 0;
        let mut stdout = io::stdout();
        // Make sure everything's flushed before FIXME Sometimes not work?
        let _ = stdout.flush().unwrap();
        // This is to not print spinner on existing text
        let _ = stdout.write(b"   ").unwrap();

        loop {
            if let Ok(_) = receiver.try_recv() {
                // Wipe the spinner with spaces
                let _ = stdout.write(b"\x1b[3D   \n").unwrap();
                break;
            };

            // Pace the spinning animation
            thread::sleep(Duration::from_millis(100));

            // Write the next animation frame
            i += 1;
            let _ = stdout.write(sequences[i % 4]).unwrap();
            let _ = stdout.flush().unwrap();
        }
    });

    // Run the job
    let result = concrete_job();
    // When finished, signal spinner to terminate
    sender.send(true).unwrap();
    // Wait for the termination
    let _ = spinner_job.join();
    result
}
