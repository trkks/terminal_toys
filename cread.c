#include <fcntl.h>
#include <stdio.h>
#include <termios.h>
#include <unistd.h>


static struct termios old_config;
static struct termios new_config;

void setup(void) {
    tcgetattr(STDIN_FILENO, &old_config);
    new_config = old_config;
    new_config.c_lflag = new_config.c_lflag & ~ICANON & ~ECHO;
    tcsetattr(STDIN_FILENO, TCSANOW, &new_config);
    fcntl(STDIN_FILENO, F_SETFL, fcntl(STDIN_FILENO, F_GETFL) | O_NONBLOCK);
}

int read_char(void) {
    return getchar();
}

void teardown(void) {
    tcsetattr(STDIN_FILENO, TCSANOW, &old_config);
}
