// frama-c -wp -wp-prover CVC4 factorial.c
// fails because of overflow

/*@
logic integer factorial(integer n) =
  (n==0) ? 1 :
  factorial(n-1)*n;
*/

/*@
  requires n >= 0;
  ensures \result == factorial(n);
  assigns \nothing;
*/
int factorial(int n) {
  int r = 1;
  int i = 0;
  /*@
    loop invariant r==factorial(i);
    loop invariant i<=n;
    loop assigns i,r;
    loop variant n-i;
  */
  while (i != n) {
    //@assert r==factorial(i);
    i++;
    //@assert r==factorial(i-1);
    r = r*i;
    //@assert r==factorial(i-1)*i;
    //@assert factorial(i-1)*i==factorial(i); // not necessarily true b/c of overflow
    //@assert r==factorial(i);
  }
  return r;
}
