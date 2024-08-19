extern struct int_queue *mallocIntQueue();
/*@ spec mallocIntQueue();
    requires true;
    ensures take R = Block<struct int_queue>(return);
@*/ 

extern void freeIntQueue (struct int_queue *p);
/*@ spec freeIntQueue(pointer p);
    requires take P = Block<struct int_queue>(p);
    ensures true;
@*/

extern struct int_queueCell *mallocIntQueueCell();
/*@ spec mallocIntQueueCell();
    requires true;
    ensures take R = Block<struct int_queueCell>(return);
@*/ 

extern void freeIntQueueCell (struct int_queueCell *p);
/*@ spec freeIntQueueCell(pointer p);
    requires take P = Block<struct int_queueCell>(p);
    ensures true;
@*/
