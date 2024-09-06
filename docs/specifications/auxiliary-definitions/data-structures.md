# Data Structures

CN supports defining tagged union (also known as sum type or algebraic) data
structures.

!!! info
    TODO: Why define custom data structures?  In the future, we'll extend this
    documentation to explain how to use CN data structures to verify the
    functional correctness of C algorithms.

# Defining new data structure types

The `datatype` keyword defines a new data structure type.  It uses this syntax:

```c
/*@
  datatype <name> {
    <constructor name> {<ctype> <field name>, ...},
    ...
  }
*@/
```

For example, here's how to define a list of `int`:
```c
/*@
  datatype int_list {
    Nil {},
    Cons {i32 hd, datatype int_list tl}
  }
*@/
```

# Data structure operations

Once you've defined a new data structure, there are a few ways to use it.

## Creating new data structures

Create an instance of the data type by invoking its constructor.  Using `int_list` as an example:
```c
/*@
  // This is a list with a single node
  Cons {hd: 0i32, tl: Nil{}}
@*/
```

## Matching values

Unlike a C `union`, CN data structures are tagged with their constructor type.
You can use the `match` keyword to break down an instance of the data struture
and reason about each constructor individually.

```c
/*@
  match my_int_list {
    // If the list is empty...
    Nil {} => { 0i32 }

    // If the list has one element...
    Cons {hd : x1, tl: Nil{} } => { x1 }

    // If the list has at least two elements...
    Cons {hd : x1, tl: Cons {hd: x2, tl: _ } } => { x1 }
  }
@*/
```
