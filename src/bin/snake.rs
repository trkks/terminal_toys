use std::io::Write;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use std::time;

use terminal_toys::snake::{GameObject, Input, SnakeGame};

extern "C" {
    #[allow(dead_code)]
    fn dequeue_input() -> Input;
}

const W: usize = 20;
const H: usize = 10;
const WALL: char = '#';

#[link(name = "cread")]
extern "C" {
    fn setup();
    fn read_char() -> i32;
    fn teardown();
}

fn input_loop(
    input_sender: mpsc::Sender<Input>,
    quit_sender: Arc<Mutex<mpsc::Sender<()>>>,
    quit_rec: Arc<Mutex<mpsc::Receiver<()>>>,
) -> impl FnOnce() -> () {
    move || {
        unsafe {
            setup();
        }
        loop {
            if let Ok(()) = quit_rec.lock().unwrap().try_recv() {
                break;
            }

            let c = unsafe { read_char() as u8 };

            let input = match c {
                b'w' => Input::Up,
                b's' => Input::Down,
                b'a' => Input::Left,
                b'd' => Input::Right,
                _ => Input::Undefined,
            };
            if let Input::Undefined = input {
                if c == b'q' {
                    quit_sender.lock().unwrap().send(()).unwrap();
                    // Move back to the bottom.
                    println!("\x1b[{}E", H + 1);
                    break;
                }
            } else if input_sender.send(input).is_err() {
                break;
            }
        }
        unsafe {
            teardown();
        }
    }
}

fn game_loop(
    quit_sender: Arc<Mutex<mpsc::Sender<()>>>,
    input_rec: mpsc::Receiver<Input>,
    quit_rec: Arc<Mutex<mpsc::Receiver<()>>>,
) -> impl FnOnce() -> () {
    let mut game = SnakeGame::new(W, H).unwrap();

    let horizontal_edge = std::iter::repeat(WALL).take(W + 2).collect::<String>();

    move || loop {
        if quit_rec.lock().unwrap().try_recv().is_ok() {
            break;
        }

        let input = match input_rec.try_recv() {
            Ok(x) => x,
            _ => Input::Undefined,
        };

        game.queue_input(input);

        let render = |board: &[GameObject]| {
            let mut view = String::with_capacity(W * H + W * 2 + H * 3);

            for line in board.chunks(W) {
                view.push(WALL);
                line.iter().for_each(|g| view.push(char_from(g)));
                view.push(WALL);
                view.push('\n');
            }

            format!(
                "{}\n{}{}\x1b[{}D\x1b[{}A",
                horizontal_edge,
                view,
                horizontal_edge,
                W + 2,
                H + 1,
            )
        };

        let draw = |x: String| {
            let stdout = std::io::stdout();
            let mut stdout_handle = stdout.lock();
            let _ = stdout_handle.write(x.as_bytes());
            let _ = stdout_handle.flush();
        };

        let game_status = game.next_frame();

        draw(render(game.board()));

        if let Err(e) = game_status {
            // Move to bottom in order to show the end result nicely.
            println!("\x1b[{}E\n{}", H + 1, e);
            quit_sender.lock().unwrap().send(()).unwrap();
            break;
        }

        thread::sleep(time::Duration::from_millis(100));
    }
}

fn char_from(g: &GameObject) -> char {
    match g {
        GameObject::Apple => 'A',
        GameObject::Body => 'S',
        GameObject::Floor => '.',
        GameObject::Head => 'H',
        GameObject::Overlap => 'X',
    }
}

fn main() {
    let (input_sender, input_receiver) = mpsc::channel();
    let (quit_sender, quit_receiver) = mpsc::channel();
    let quit_sender = Arc::new(Mutex::new(quit_sender));
    let quit_receiver = Arc::new(Mutex::new(quit_receiver));

    let input = thread::spawn(input_loop(
        input_sender,
        Arc::clone(&quit_sender),
        Arc::clone(&quit_receiver),
    ));
    let game = thread::spawn(game_loop(quit_sender, input_receiver, quit_receiver));

    let _ = game.join();
    let _ = input.join();
}
