extern struct queue *mallocIntQueue();
/*@ spec mallocIntQueue();
    requires true;
    ensures take R = Block<struct queue>(return);
@*/ 

extern void freeIntQueue (struct queue *p);
/*@ spec freeIntQueue(pointer p);
    requires take P = Block<struct queue>(p);
    ensures true;
@*/

extern struct queue_cell *mallocIntqueue_cell();
/*@ spec mallocIntqueue_cell();
    requires true;
    ensures take R = Block<struct queue_cell>(return);
@*/ 

extern void freeIntqueue_cell (struct queue_cell *p);
/*@ spec freeIntqueue_cell(pointer p);
    requires take P = Block<struct queue_cell>(p);
    ensures true;
@*/
