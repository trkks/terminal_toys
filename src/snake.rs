use std::collections::VecDeque;


pub struct SnakeGame {
    board: Vec<char>,
    board_size: V2,
    snake: Vec<V2>,
    apple: V2,
    dir: V2,
    horizontal_edge: String,
    input_queue: VecDeque<Input>,
}

impl SnakeGame {
    pub fn new(width: usize, height: usize) -> Result<Self, String> { 
        let board = vec!['.'; width * height];
        let board_size = V2 { x: width as i32, y: height as i32 };
        let snake = vec![V2 { x: 5, y: 5}, V2 { x: 6, y: 5}];
        let apple = V2 { x: 9, y: 3 };
        let dir = V2 { x: 0, y: -1 };
        let horizontal_edge = String::from_utf8(
            std::iter::repeat(b'#').take(board_size.x as usize + 2).collect::<Vec<u8>>()
        )
        .unwrap();
        let input_queue = VecDeque::new();

        Ok(
            Self {
                board, board_size, snake, apple, dir, horizontal_edge, input_queue,
            }
        )
    }

    pub fn queue_input(&mut self, input: Input) {
        self.input_queue.push_back(input);
    }

    pub fn next(&mut self) -> Result<String, String> {
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
            let (width, height) = (self.board_size.x as i32, self.board_size.y as i32);
            let keep_in_bounds = |p: &mut V2| {
                if p.x < 0            { p.x += width;  }
                else if width <= p.x  { p.x -= width;  }
                if p.y < 0            { p.y += height; }
                else if height <= p.y { p.y -= height; }
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
            self.apple.x = (rand::random::<f32>() * self.board_size.x as f32) as i32;
            self.apple.y = (rand::random::<f32>() * self.board_size.y as f32) as i32;
        }

        for part in self.board.iter_mut() {
            *part = '.';
        }
        self.board[(self.snake[0].y * self.board_size.x as i32 + self.snake[0].x) as usize] = 'H';
        for p in self.snake.iter().skip(1) {
            self.board[(p.y * self.board_size.x as i32 + p.x) as usize] = 'S';
        }
        self.board[(self.apple.y * self.board_size.x as i32 + self.apple.x) as usize] = 'A';

        let render = |board: &[char], horizontal_edge: &str, board_size: V2| {
            let mut view =
                String::with_capacity(board.len() + board_size.x as usize * 2 + board_size.y as usize * 3);
            for line in board.chunks(board_size.x as usize) {
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
                board_size.x + 2, board_size.y + 1,
            )
        };
        let snake_ate_self = self.snake[1..].iter()
            .any(|p| p.x == self.snake[0].x && p.y == self.snake[0].y);
        if snake_ate_self {
            self.board[(self.snake[0].y * self.board_size.x as i32 + self.snake[0].x) as usize] = 'X';
            return Err(format!("{}\nGame over", render(&self.board, &self.horizontal_edge, self.board_size)));
        }

        Ok(render(&self.board, &self.horizontal_edge, self.board_size))
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
pub enum Input {
    Undefined,
    Up,
    Down,
    Left,
    Right,
}
