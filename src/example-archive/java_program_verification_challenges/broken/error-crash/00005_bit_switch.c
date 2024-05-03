// Tags: main, switch, java

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Title: Typical Mode Selection Based on Com m and Byte.


   Description: Our next example in Figure 5 is not of the sort one
finds in textbooks on program verification. But it is a good example
of the ugly code that verification tools have to deal with in
practice, specifically in Java Card applets6. It involves a “command”
byte cmd which is split in two parts: the first three, and last five
bits. Depending on these parts, a mode field is given an appropriate
value. This happens in a nested switch. The specification is helpful
because it tells in decimal notation what is going on.

*/
//#include <stdio.h>
#include <stdlib.h>

#define ACTION_ONE   1
#define ACTION_TWO   2
#define ACTION_THREE 3
#define ACTION_FOUR  4

// Error codes to mimic exception throwing
#define ERROR_INVALID_COMMAND -1

// Specifying mode as a publicly accessible but encapsulated variable
static unsigned char mode;

/* Behavior
 * @ requires true;
 * @ assignable mode;
 * @ ensures (cmd == 0 && mode == ACTION_ONE) ||
 *           (cmd == 16 && mode == ACTION_TWO) ||
 *           (cmd == 4 && mode == ACTION_THREE) ||
 *           (cmd == 20 && mode == ACTION_FOUR);
 * @ signals (Exception)
 *           ((cmd & 0x07) != 0 && (cmd != 0 && cmd != 16)) ||
 *           ((cmd & 0x07) != 4 && (cmd != 4 && cmd != 20));
 */
int select_mode(unsigned char cmd) {
    unsigned char cmd1 = cmd & 0x07, cmd2 = cmd >> 3;

    switch (cmd1) {
        case 0x00:
            switch (cmd2) {
                case 0x00:
                    mode = ACTION_ONE;
                    break;
                case 0x02:
                    mode = ACTION_TWO;
                    break;
                default:
                    return ERROR_INVALID_COMMAND; // Exception handling via error code
            }
            break;
        case 0x04:
            switch (cmd2) {
                case 0x00:
                    mode = ACTION_THREE;
                    break;
                case 0x02:
                    mode = ACTION_FOUR;
                    break;
                default:
                    return ERROR_INVALID_COMMAND; // Exception handling via error code
            }
            break;
        default:
            return ERROR_INVALID_COMMAND; // Exception handling via error code
    }
    return 0; // Success
}

int main() {
    // Example usage
    int result = select_mode(0x00); // Should set mode to ACTION_ONE
    /* if (result == ERROR_INVALID_COMMAND) { */
    /*     printf("Invalid command\n"); */
    /* } else { */
    /*     printf("Mode selected: %d\n", mode); */
    /* } */
    return 0;
}
