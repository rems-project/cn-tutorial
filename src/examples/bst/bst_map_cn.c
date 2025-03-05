#include <stdlib.h>
#include <assert.h>

#include "bst_map_cn.h"

struct MapNode *malloc_MapNode() {
  struct MapNode *result = malloc(sizeof(struct MapNode));
  assert(result != NULL);
  return result;
}
