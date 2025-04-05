// frama-c -wp -wp-rte -wp-prover CVC5 hoare.c

#include <limits.h>

#define LIMIT INT_MAX/2

/*@
  requires bar >= 0;
  requires bar < LIMIT;
  ensures \result == -2 * bar;
  assigns \nothing;
 */
int ex(int bar) {
  int foo = 0;
  int baz = 0;
  /*@
    loop invariant baz == -2 * foo;
    loop invariant bar >= foo;
    loop assigns foo, baz;
    loop variant bar-foo;
  */
  while (foo != bar) {
    baz = baz - 2;
    foo = foo + 1;
  }
  return baz;
}
