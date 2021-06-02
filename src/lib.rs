use std::io::{self, Write};
use std::sync::mpsc;
use std::time::Duration;
use std::thread;

pub mod snake;
pub mod progress_bar;


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