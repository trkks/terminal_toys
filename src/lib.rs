pub mod snake;
pub mod progress_bar;
pub mod spinner;
pub mod smargs;

// Re-exports the struct to be directly used from `terminal_toys`
pub use progress_bar::ProgressBar;
pub use smargs::Smargs;
