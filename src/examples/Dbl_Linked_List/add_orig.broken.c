#include "./headers.h"

// Adds after the given node and returns a pointer to the new node
struct node *add(int element, struct node *n)
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->prev = 0;
    new_node->next = 0;

    if (n == 0) //empty list case
    {
        new_node->prev = 0;
        new_node->next = 0;
        return new_node;
    } else { 
        new_node->next = n->next;
        new_node->prev = n;

        if (n->next !=0) {
            n->next->prev = new_node;
        }

        n->next = new_node;
        return new_node;
    }
}