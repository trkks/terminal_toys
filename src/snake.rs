use std::thread;
use std::time;
use std::sync::{Arc, Mutex, mpsc};
use std::io::Write;

pub fn play() {
    let (input_sender, input_receiver) = mpsc::channel();
    let (quit_sender, quit_receiver) = mpsc::channel();
    let quit_sender = Arc::new(Mutex::new(quit_sender));
    let quit_receiver = Arc::new(Mutex::new(quit_receiver));

    let input = InputHandler::new(
        input_sender,
        Arc::clone(&quit_sender),
        Arc::clone(&quit_receiver),
    );
    let logic = LogicHandler::new(
        quit_sender,
        input_receiver,
        quit_receiver,
    );

    let _ = input.0.join();
    let _ = logic.0.join();
}

const W: usize = 20;
const H: usize = 10;

struct InputHandler(thread::JoinHandle<()>);
impl InputHandler {
    fn new(
        input_sender: mpsc::Sender<Input>,
        quit_sender: Arc<Mutex<mpsc::Sender<()>>>,
        quit_rec: Arc<Mutex<mpsc::Receiver<()>>>,
    ) -> Self {
        let stdin = std::io::stdin();
        let handle = thread::spawn(move || loop {
            if let Ok(()) = quit_rec.lock().unwrap().try_recv() {
                break;
            }
            let mut s = String::new();
            stdin.read_line(&mut s).unwrap();  // Blocks
            let input = match &s.as_str().trim().to_lowercase()[..] {
                "w" => Input::Up,
                "s" => Input::Down,
                "a" => Input::Left,
                "d" => Input::Right,
                _   => Input::Undefined,
            };
            if let Input::Undefined = input {
                if s.contains("q") {
                    quit_sender.lock().unwrap().send(()).unwrap();
                    break;
                }
            } else if let Err(_) = input_sender.send(input) {
                break;
            }
        });

        Self(handle)
    }
}
struct LogicHandler(thread::JoinHandle<()>);
impl LogicHandler {
    fn new(
        quit_sender: Arc<Mutex<mpsc::Sender<()>>>,
        input_rec: mpsc::Receiver<Input>,
        quit_rec: Arc<Mutex<mpsc::Receiver<()>>>,
    ) -> Self {
        let mut board: [char;W*H] = ['.';W*H];
        let mut snake = vec![V2 { x: 5, y: 5}, V2 { x: 6, y: 5}];
        let mut apple = V2 { x: 9, y: 3 };
        let mut dir = V2 { x: 0, y: -1 };
        let horizontal_edge = String::from_utf8(
            std::iter::repeat('#' as u8).take(W + 2).collect::<Vec<u8>>()
        )
        .unwrap();
        let logic_handle = thread::spawn(move || loop {
            if let Ok(_) = quit_rec.lock().unwrap().try_recv() {
                break;
            }
            let input = match input_rec.try_recv() {
                Ok(x) => x,
                _ => Input::Undefined,
            };
            match input {
                Input::Up    => dir = V2 { x: 0, y:-1 },
                Input::Down  => dir = V2 { x: 0, y: 1 },
                Input::Left  => dir = V2 { x:-1, y: 0 },
                Input::Right => dir = V2 { x: 1, y: 0 },
                // TODO Set head to LAST (reversed) from some input?
                _            => { },
            };

            let mut last_head = snake[0];
            snake[0] = {
                let mut new_p = snake[0].add(&dir);
                if new_p.x < 0              { new_p.x = W as i32 - 1; }
                else if W as i32 <= new_p.x { new_p.x = 0;            }
                if new_p.y < 0              { new_p.y = H as i32 - 1; }
                else if H as i32 <= new_p.y { new_p.y = 0;            }
                new_p
            };

            for i in 1..snake.len() {
                let temp = snake[i];
                snake[i] = last_head;
                last_head = temp;
            }

            if snake[0].x == apple.x && snake[0].y == apple.y {
                snake.push(snake[snake.len()-1]);
                apple.x = (rand::random::<f32>() * W as f32) as i32;
                apple.y = (rand::random::<f32>() * H as f32) as i32;
            }

            for i in 0..W*H {
                board[i] = '.';
            }
            board[(snake[0].y * W as i32 + snake[0].x) as usize] = 'H';
            snake.iter()
                .skip(1)
                .for_each(|p| board[(p.y * W as i32 + p.x) as usize] = 'S');
            board[(apple.y * W as i32 + apple.x) as usize] = 'A';

            let mut view = String::with_capacity(board.len() + W * 2 + H * 3);
            for line in board.chunks(W) {
                view.push('#');
                line.iter().for_each(|&c| view.push(c));
                view.push('#');
                view.push('\n');
            }

            {
                let stdout = std::io::stdout();
                let mut stdout_handle = stdout.lock();
                let _ = stdout_handle.write(
                    format!(
                        "\x1b[2J\x1b[0;0H{}\n{}{}",
                        horizontal_edge,
                        view,
                        horizontal_edge,
                    )
                    .as_bytes()
                );
                let _ = stdout_handle.flush();
            }

            let snake_ate_self = snake[1..].iter()
                .any(|p| p.x == snake[0].x && p.y == snake[0].y);
            if snake_ate_self {
                println!("\nGAME OVER. ([RETURN] to quit)");
                quit_sender.lock().unwrap().send(()).unwrap();
                break;
            }

            thread::sleep(time::Duration::from_millis(200));
        });

        Self(logic_handle)
    }
}

#[derive(Clone,Copy)]
struct V2 { x: i32, y: i32 }
impl V2 {
    fn add(&self, other: &V2) -> Self {
        V2 { x: self.x + other.x, y: self.y + other.y }
    }
}

enum Input {
    Undefined,
    Up,
    Down,
    Left,
    Right,
}
