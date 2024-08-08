#include "./headers.h"
#include "./functions.h"

int main()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
    pop_back(q);
    free_dbl_queue(q);

    return 0;
}