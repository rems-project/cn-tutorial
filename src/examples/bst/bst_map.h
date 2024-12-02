#ifndef SET_H
#define SET_H
/* A set defined as binary search tree */

#include <stdbool.h>

#define KEY    int
#define VALUE  long

struct MapNode {
  KEY key;
  int ignore;
  VALUE value; 
  struct MapNode *smaller;
  struct MapNode *larger;
};

struct MapNode* malloc_MapNode();


struct Map {
  struct MapNode *root;
};

struct Map map_empty();
bool map_lookup(struct Map map, KEY key, VALUE *value);


#endif // SET_H
