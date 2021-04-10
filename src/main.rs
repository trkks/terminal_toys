use terminal_toys::{ProgressBar};

fn main() {
    // Spawn some threads with their own progress bars for demonstration

    let n = 10_000_000;
    let threads = match std::env::args().skip(1).next() {
        Some(arg) => arg.parse().unwrap_or(0),
        None      => {
            eprintln!("Please provide an amount of threads to spawn");
            std::process::exit(1);
        }
    };

    // Clear terminal 
    println!("\x1b[2J");
    
    let mut handles = vec![];
    for i in 0..threads {
        let mut pb1 = ProgressBar::new(n, 10);
        pb1.title(&format!("Thread #{}", i));
        handles.push(
            std::thread::spawn(move || {
                for _ in 0..n {
                    pb1.print_update_row(i+1).unwrap();
                }
            })
        );
    }

    // Join all threads
    for handle in handles.into_iter() {
        handle.join().unwrap(); 
    }

    // Move back to bottom row
    println!("\x1b[{};0f", threads);
}
