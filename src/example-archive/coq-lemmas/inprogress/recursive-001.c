#include <stdbool.h>
/*@

datatype a_list {
  LsNil {},
  LsCons {u32 i, a_list t}
}

@*/

/* The predicates relating A/B trees to their C encoding. */

enum {
  NUM_NODES = 16,
  LEN_LIMIT = (1 << 16),
};

struct node;

typedef struct node * tree;

struct node {
  int v;
  tree nodes[NUM_NODES];
};

/*@


  
datatype tree_arc {
  Arc_End {},
  Arc_Step {i32 i, datatype tree_arc tail}
}

datatype tree_node_option {
  Node_None {},
  Node {i32 v}
}

function (map<datatype tree_arc, datatype tree_node_option>) empty ()
function (map<datatype tree_arc, datatype tree_node_option>) construct
    (i32 v, map<i32, map<datatype tree_arc, datatype tree_node_option> > ts)

function (map<i32, map<datatype tree_arc, datatype tree_node_option> >) default_ns ()

predicate {map<datatype tree_arc, datatype tree_node_option> t,
        i32 v, map<i32, map<datatype tree_arc, datatype tree_node_option> > ns}
  Tree (pointer p)
{
  if (is_null(p)) {
    return {t: (empty ()), v: 0i32, ns: default_ns ()};
  }
  else {
    take V = Owned<int>(member_shift<node>(p,v));
    let nodes_ptr = member_shift<node>(p,nodes);
    take Ns = each (i32 i; (0i32 <= i) && (i < (num_nodes ())))
      {Indirect_Tree(array_shift<tree>(nodes_ptr, i))};
    let t = construct (V, Ns);
    return {t: t, v: V, ns: Ns};
  }
}
@*/


/*

  match ls {
    LsNil {} =>
      take value = Owned<struct a_node>(p);
      assert (value[0] == 0);
      assert (is_null(p+1));
      return 0;
    LsCons {u32 i, a_list tl} =>
      take value = Owned<struct a_node>(p);
      assert(value[0] == i);
      assert (is_array(p+1, tl))
      return i;
      }
  
 */
void trivial() 
{
  ; 
}
