use std::collections::VecDeque;
use std::io::Write;
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time;


extern "C" {
    #[allow(dead_code)]
    fn dequeue_input() -> Input;
}

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
        let mut game = SnakeGame::new().unwrap();
        let logic_handle = thread::spawn(move || loop {
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
        });

        Self(logic_handle)
    }
}

type Board = [char; W * H];

struct SnakeGame {
    board: Board,
    snake: Vec<V2>,
    apple: V2,
    dir: V2,
    horizontal_edge: String,
    input_queue: VecDeque<Input>,
}

impl SnakeGame {
    fn new() -> Result<Self, String> { 
        let board = ['.'; W * H];
        let snake = vec![V2 { x: 5, y: 5}, V2 { x: 6, y: 5}];
        let apple = V2 { x: 9, y: 3 };
        let dir = V2 { x: 0, y: -1 };
        let horizontal_edge = String::from_utf8(
            std::iter::repeat(b'#').take(W + 2).collect::<Vec<u8>>()
        )
        .unwrap();
        let input_queue = VecDeque::new();

        Ok(
            Self {
                board, snake, apple, dir, horizontal_edge, input_queue,
            }
        )
    }

    fn queue_input(&mut self, input: Input) {
        self.input_queue.push_back(input);
    }

    fn next(&mut self) -> Result<String, String> {
        let input = self.input_queue
            .pop_front()
            .unwrap_or(Input::Undefined);
        match input {
            Input::Up    => self.dir = V2 { x: 0, y:-1 },
            Input::Down  => self.dir = V2 { x: 0, y: 1 },
            Input::Left  => self.dir = V2 { x:-1, y: 0 },
            Input::Right => self.dir = V2 { x: 1, y: 0 },
            _            => { },
        };

        let mut last_head = self.snake[0];
        self.snake[0] = {
            let keep_in_bounds = |p: &mut V2| {
                if p.x < 0              { p.x += W as i32; }
                else if W as i32 <= p.x { p.x -= W as i32; }
                if p.y < 0              { p.y += H as i32; }
                else if H as i32 <= p.y { p.y -= H as i32; }
            };

            let mut new_p = self.snake[0].add(&self.dir);
            keep_in_bounds(&mut new_p);

            if new_p == self.snake[1] {
                // Reverse the snake.
                self.snake = self.snake.clone().into_iter().rev().collect();
                // Set direction to the "opposite" of previous tail.
                match self.snake[0].sub(&self.snake[1]) {
                    d if d.x.abs() <= 1 && d.y.abs() <= 1 => self.dir = d,
                    // Do nothing to handle the case where two successive
                    // segments are at opposite edges.
                    _ => { },
                };

                last_head = self.snake[0];
                new_p = self.snake[0].add(&self.dir);
            }

            keep_in_bounds(&mut new_p);

            new_p
        };

        for part in self.snake.iter_mut().skip(1) {
            std::mem::swap(part, &mut last_head);
        }

        if self.snake[0].x == self.apple.x && self.snake[0].y == self.apple.y {
            self.snake.push(self.snake[self.snake.len()-1]);
            self.apple.x = (rand::random::<f32>() * W as f32) as i32;
            self.apple.y = (rand::random::<f32>() * H as f32) as i32;
        }

        for part in self.board.iter_mut() {
            *part = '.';
        }
        self.board[(self.snake[0].y * W as i32 + self.snake[0].x) as usize] = 'H';
        for p in self.snake.iter().skip(1) {
            self.board[(p.y * W as i32 + p.x) as usize] = 'S';
        }
        self.board[(self.apple.y * W as i32 + self.apple.x) as usize] = 'A';

        let render = |board: &[char], horizontal_edge: &str| {
            let mut view =
                String::with_capacity(board.len() + W * 2 + H * 3);
            for line in board.chunks(W) {
                view.push('#');
                line.iter().for_each(|&c| view.push(c));
                view.push('#');
                view.push('\n');
            }

            format!(
                "{}\n{}{}\x1b[{}D\x1b[{}A",
                // Save upper left corner for showing the input
                // (...and thus wrapping the top edge nicely).
                &horizontal_edge[1..],
                view,
                &horizontal_edge,
                W + 2, H + 1,
            )
        };
        let snake_ate_self = self.snake[1..].iter()
            .any(|p| p.x == self.snake[0].x && p.y == self.snake[0].y);
        if snake_ate_self {
            self.board[(self.snake[0].y * W as i32 + self.snake[0].x) as usize] = 'X';
            return Err(format!("{}\nGame over", render(&self.board, &self.horizontal_edge)));
        }

        Ok(render(&self.board, &self.horizontal_edge))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct V2 { x: i32, y: i32 }
impl V2 {
    fn add(&self, other: &V2) -> Self {
        V2 { x: self.x + other.x, y: self.y + other.y }
    }

    fn sub(&self, other: &V2) -> Self {
        V2 { x: self.x - other.x, y: self.y - other.y }
    }
}

#[repr(C)]
enum Input {
    Undefined,
    Up,
    Down,
    Left,
    Right,
}
