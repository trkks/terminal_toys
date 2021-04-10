use terminal_toys::{ProgressBar, start_spinner};

fn main() {
    //progressbar_thread_test();
    spinner_test();
}

fn spinner_test() {
    let n = 1_000_000_00;
    let make_lots_of_halves = move|| {
        // This'd be more fitting as an iterator, but it is evaluated instantly
        let mut xs = Vec::new();
        xs.reserve(n);
        for i in 2..n+2 {
            xs.push(i/2);
        }
        xs.into_iter()
    };

    print!("Running loop job ");
    let halves = start_spinner(Box::new(make_lots_of_halves));
    //let halves = make_lots_of_halves(n);
    print!("Done! Calculating result ");
    let add_mod_threes = ||halves.fold(1,|acc,x|if x%3==0{acc+1}else{acc});
    let result = start_spinner(Box::new(add_mod_threes));
    //let result = add_mod_threes(halves);
    println!("The results are in: {}", result);
}

/// Spawn some threads with their own progress bars for demonstration
fn progressbar_thread_test() {
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
