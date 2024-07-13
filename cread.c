#include <stdio.h>
#include <termios.h>
#include <unistd.h>


static struct termios old_config;
static struct termios new_config;

void setup(void) {
    tcgetattr(STDIN_FILENO, &old_config);
    new_config = old_config;
    new_config.c_lflag = new_config.c_lflag & ~ICANON;
    tcsetattr(STDIN_FILENO, TCSANOW, &new_config);
}

int read_char(void) {
    return getchar();
}

void teardown(void) {
    tcsetattr(STDIN_FILENO, TCSANOW, &old_config);
}
