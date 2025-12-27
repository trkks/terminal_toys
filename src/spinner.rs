use std::io::{self, Write};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

pub trait Animation {
    type Output;
    fn start<B: io::Write>(buffer: B) -> io::Result<(Self::Output, Self)>
    where
        Self: Sized;
    fn update<B: io::Write>(&mut self, buffer: B) -> io::Result<Self::Output>;
    fn finish<B: io::Write>(&mut self, buffer: B) -> io::Result<usize>;
}

struct Spinner {
    frames: usize,
}

impl Animation for Spinner {
    type Output = ();

    // # Panics
    // This will panic if writing the buffer fails for some reason.
    fn start<B: io::Write>(mut buffer: B) -> io::Result<(Self::Output, Self)> {
        // This is to not print spinner on existing text
        let _ = buffer.write(b"   ").unwrap();
        Ok(((), Self { frames: 0 }))
    }

    // # Panics
    // This will panic if writing or flushing the buffer fails for some reason.
    fn update<B: io::Write>(&mut self, mut buffer: B) -> io::Result<Self::Output> {
        // Pace the spinning animation
        thread::sleep(Duration::from_millis(100));

        self.frames += 1;
        const SEQUENCES: [&[u8; 7]; 4] =
            [b"\x1b[3D(|)", b"\x1b[3D(/)", b"\x1b[3D(-)", b"\x1b[3D(\\)"];

        let _ = buffer.write(SEQUENCES[self.frames % 4]).unwrap();
        buffer.flush().unwrap();

        Ok(())
    }

    fn finish<B: io::Write>(&mut self, mut buffer: B) -> io::Result<usize> {
        // Wipe the spinner with spaces
        buffer.write(b"\x1b[3D   \n")
    }
}

/// Starts a spinner animation at the current terminal print position
/// that runs until the end of `concrete_job`, showing that it is processing
/// # Example:
/// ```
/// let result = terminal_toys::spinner::start_spinner(||
///     std::iter::repeat(2).take(20).fold(44040192, |acc, x| acc / x)
/// ).unwrap();
/// // (The spinner spins at the end of the line while computing the result)
/// assert_eq!(result, 42);
/// ```
pub fn start_spinner<T, F>(job: F) -> io::Result<T>
where
    F: FnOnce() -> T,
{
    // Start the concrete job and in another thread, run the spinner
    // When concrete job finishes, call join on the spinner-thread

    let (sender, receiver) = mpsc::channel();

    // Start the spinner in another thread
    let spinner_job = thread::spawn(move || {
        // Make sure everything's flushed before FIXME Sometimes not work?
        let mut stdout = io::stdout();
        stdout.flush().unwrap();

        let mut spinner = Spinner::start(&stdout).unwrap().1;

        loop {
            if receiver.try_recv().is_ok() {
                break spinner.finish(&stdout);
            };

            // Write the next animation frame
            spinner.update(&stdout)?;
        }
    });

    // Run the job
    let result = job();
    // When finished, signal spinner to terminate
    sender.send(true).unwrap();
    // Wait for the termination
    spinner_job.join().unwrap().map(|_| result)
}
