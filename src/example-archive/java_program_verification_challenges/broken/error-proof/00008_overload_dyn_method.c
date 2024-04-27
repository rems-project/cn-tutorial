// Tags: main, java, predicates, function pointers

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Title: Overloading and Dynamic Method Invocation.

   Description: The example in Figure 8 is usually attributed to Kim
Bruce. It addresses an issue which is often thought of as confusing in
programming with languages which support inheritance. When overriding
a method the run-time type of an object decides which method is
called. This phenomena is also called late-binding. In the example
three different objects are created, and the question is which equal
method will be called.  Notice that the equal methods have no
specifications. According to the JML semantics, the equal method in
class Point should also satisfy the specification from the equal
method in class ColorPoint. This makes it impossible to prove a
precise specification of the equal method in class Point. Therefore we
proved the specification of method m() by using the implementations of
the equal methods.  The result that most programmers find surprising
comes from the assignment r8 = p2.equal(cp). The static type of the
expression p2 is Point, so that according to the first step in
processing a method invocation at compile-time ([13, Section
15.12.1]), the equal method of Point is used.

*/

//#include <stdio.h>

/*@
predicate { u32 pv, u32 qv } BothOwned (pointer p, pointer q)
{
  if (p == q) {
    take pv = Owned<Point>(p);
    return {pv: pv, qv: pv};
  }
  else {
    take pv = Owned<Point>(p);
    take qv = Owned<Point>(q);
    return {pv: pv, qv: qv};
  }
}
@*/

// Define structures for Point and ColorPoint
typedef struct Point {
    int (*equal)(struct Point *self, struct Point *other);
} Point;

typedef struct ColorPoint {
    Point base;
    int (*equal)(struct ColorPoint *self, struct ColorPoint *other);
} ColorPoint;

// Function declarations
int Point_equal(Point *self, Point *other) {
    return 1;
}

int ColorPoint_equal(ColorPoint *self, ColorPoint *other) {
    return 2;
}

// Wrapper functions for handling inheritance
int Point_equal_wrapper(Point *self, Point *other) 
  /*@ requires take vs0 = BothOwned(self,other)
      ensures take vs1 = BothOwned(self,other)
  @*/
  {
    // Direct call to the function based on actual type
    if (self->equal == (int (*)(Point *, Point *))ColorPoint_equal) {
        return ((ColorPoint *)self)->equal((ColorPoint *)self, (ColorPoint *)other);
    }
    return self->equal(self, other);
}

// Main function demonstrating the use of the above classes and methods
int main() {
    int r1, r2, r3, r4, r5, r6, r7, r8, r9;

    // Initializing the Point and ColorPoint
    Point pl = { Point_equal };
    Point p2 = { (int (*)(Point *, Point *))ColorPoint_equal };
    ColorPoint cp = { { Point_equal }, ColorPoint_equal };

    // Simulating the method calls
    r1 = Point_equal_wrapper(&pl, &pl);
    r2 = Point_equal_wrapper(&pl, &p2);
    r3 = Point_equal_wrapper(&p2, &pl);
    r4 = Point_equal_wrapper(&p2, &p2);
    r5 = Point_equal_wrapper((Point *)&cp, &pl);
    r6 = Point_equal_wrapper((Point *)&cp, &p2);
    r7 = Point_equal_wrapper(&pl, (Point *)&cp);
    r8 = Point_equal_wrapper(&p2, (Point *)&cp);
    r9 = Point_equal_wrapper((Point *)&cp, (Point *)&cp);

    // Print results
    /* printf("r1 = %d, r2 = %d, r3 = %d, r4 = %d, r5 = %d, r6 = %d, r7 = %d, r8 = %d, r9 = %d\n", */
    /*        r1, r2, r3, r4, r5, r6, r7, r8, r9); */

    return 0;
}

