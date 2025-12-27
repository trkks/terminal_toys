use terminal_toys::ProgressBar;

/// Spawn some threads with their own progress bars for demonstration
fn main() {
    let n = 10_000_000;
    let threads = 10;

    // Visualize some progress in multiple threads with different length bars
    let mut handles = vec![];
    for (i, mut bar) in ProgressBar::multiple(n, 20, threads)
        .into_iter()
        .enumerate()
    {
        bar.title(&format!("Thread #{}", i));
        handles.push(std::thread::spawn(move || {
            let m = n / threads;
            for j in 0..m {
                let percent = j as f32 / m as f32 * 100.0;
                bar.title(&format!("Thread #{} {:>3.0}%", i, percent));
                bar.ulap();
            }
        }));
    }

    // Join all threads
    for handle in handles.into_iter() {
        handle.join().unwrap();
    }

    // Move to bottom of all progress bars
    println!("\x1b[{}B", threads);
}
