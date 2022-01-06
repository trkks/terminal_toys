use terminal_toys::ProgressBar;

/// Spawn some threads with their own progress bars for demonstration
fn main() {
    let n = 10_000_000;
    let threads = 10;

    // Print room down for the progressbars
    for _ in 0..threads {
        println!();
    }
    // Move back to top
    print!("\x1b[{}A", threads + 1);


    // Visualize some progress in multiple threads with different length bars
    let mut handles = vec![];
    for i in 0..threads {
        let bar_len = 5 * (i + 1);
        let mut pb1 = ProgressBar::new(n, bar_len);
        pb1.title(&format!("Thread #{}, bar length {:>2}", i, bar_len));
        pb1.row(i + 1);
        handles.push(
            std::thread::spawn(move || {
                for _ in 0..n {
                    pb1.print_update().unwrap();
                }
            })
        );
    }


    // Join all threads
    for handle in handles.into_iter() {
        handle.join().unwrap();
    }

    // Move to bottom of all progress bars
    println!("\x1b[{}B", threads);
}
