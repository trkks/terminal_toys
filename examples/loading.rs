use terminal_toys::{ProgressBar, start_spinner};

fn main() {
    progressbar_thread_test();
    spinner_test();
}

fn spinner_test() {
    let n = 50_000_000;
    let make_lots_of_halves = move|| {
        // TODO What does this comment even mean?:
        // This'd be more fitting as an iterator, but it is evaluated instantly
        let mut xs = Vec::new();
        xs.reserve(n);
        for i in 2..(n + 2) {
            xs.push(i / 2);
        }
        xs.into_iter()
    };

    print!("Running loop job ");
    let halves = start_spinner(make_lots_of_halves);
    print!("Done! Calculating result ");
    let add_mod_threes = ||
        halves.fold(0, |acc, x| if x % 3 == 0 { acc + 1 } else { acc });
    let result = start_spinner(add_mod_threes);
    println!("The results are in: {}", result);
}

/// Spawn some threads with their own progress bars for demonstration
fn progressbar_thread_test() {
    let n = 10_000_000;
    let threads = 10;
    // Clear terminal 
    println!("\x1b[2J");
    
    let mut handles = vec![];
    for i in 0..threads {
        let mut pb1 = ProgressBar::new(n, 5 * (i + 1));
        pb1.title(&format!("Thread #{}", i));
        handles.push(
            std::thread::spawn(move || {
                for _ in 0..n {
                    pb1.print_update_row(i + 1).unwrap();
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
