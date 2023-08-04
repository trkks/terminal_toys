use std::io::Write;
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time;

use terminal_toys::snake::{SnakeGame, Input};


extern "C" {
    #[allow(dead_code)]
    fn dequeue_input() -> Input;
}

const W: usize = 20;
const H: usize = 10;

pub fn play() {
    let (input_sender, input_receiver) = mpsc::channel();
    let (quit_sender, quit_receiver) = mpsc::channel();
    let quit_sender = Arc::new(Mutex::new(quit_sender));
    let quit_receiver = Arc::new(Mutex::new(quit_receiver));

    let input = thread::spawn(input_loop(
        input_sender,
        Arc::clone(&quit_sender),
        Arc::clone(&quit_receiver),
    ));
    let game = thread::spawn(game_loop(
        quit_sender,
        input_receiver,
        quit_receiver,
    ));

    let _ = input.join();
    let _ = game.join();
}

fn input_loop(
    input_sender: mpsc::Sender<Input>,
    quit_sender: Arc<Mutex<mpsc::Sender<()>>>,
    quit_rec: Arc<Mutex<mpsc::Receiver<()>>>,
) -> impl FnOnce() -> () {
    let stdin = std::io::stdin();
    move || loop {
        if let Ok(()) = quit_rec.lock().unwrap().try_recv() {
            break;
        }
        let mut s = String::new();
        stdin.read_line(&mut s).unwrap();  // Blocks
        // Undo the RETURN resulted from input by moving to previous line.
        print!("\x1b[F");
        let _ = std::io::stdout().flush();

        let input = match &s.as_str().trim().to_lowercase()[..] {
            "w" => Input::Up,
            "s" => Input::Down,
            "a" => Input::Left,
            "d" => Input::Right,
            _   => Input::Undefined,
        };
        if let Input::Undefined = input {
            if s.contains('q') {
                quit_sender.lock().unwrap().send(()).unwrap();
                // Move back to the bottom.
                println!("\x1b[{}E", H + 1);
                break;
            }
        } else if input_sender.send(input).is_err() {
            break;
        }
    }
}

fn game_loop(
    quit_sender: Arc<Mutex<mpsc::Sender<()>>>,
    input_rec: mpsc::Receiver<Input>,
    quit_rec: Arc<Mutex<mpsc::Receiver<()>>>,
) -> impl FnOnce() -> () {
    let mut game = SnakeGame::new(W, H).unwrap();
    move || loop {
        if quit_rec.lock().unwrap().try_recv().is_ok() {
            break;
        }
        let input = match input_rec.try_recv() {
            Ok(x) => x,
            _ => Input::Undefined,
        };
        game.queue_input(input);
        let draw = |x: String| {
            let stdout = std::io::stdout();
            let mut stdout_handle = stdout.lock();
            let _ = stdout_handle.write(x.as_bytes());
            let _ = stdout_handle.flush();
        };
        match game.next() {
            Ok(x) => draw(x),
            Err(e) => {
                draw(e);
                quit_sender.lock().unwrap().send(()).unwrap();
                break;
            },
        };
        thread::sleep(time::Duration::from_millis(100));
    }
}


fn main() {
    play()
}
