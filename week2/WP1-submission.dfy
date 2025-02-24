// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// You got this!!
//
// END-TODO(Name)



/* == Handout question 3.6 ==
 * Calculate the following weakest preconditions and simplify the result. Test
 * where possible your calculation in Dafny, using that
 * 
 * assume W;
 * S;
 * assert P;
 *
 * should verify, where W is WP(S, P). */

/* (a) WP(x := 3y − 2x, x <= y) */
method A(x: int, y: int) returns (x': int)
  // BEGIN-TODO(MethodA)
  // Add the specification and the method body here.
  // WP [x := 3y - 2x, x <= y]
  // = WP [y <=x]
  // {{y <= x}} x := 3y - 2x {{x <= y}}
  requires y <= x
  ensures x' <= y
{
  //assume y <= x;
  x' := 3*y - 2*x;
  //assert x' <=y;
}

// END-TODO(MethodA)


/* (e) WP(m := n; n := n + 1; forall i | 0 <= i < n :: s[i] <= s[m])
 * given that `forall i | 0 <= i < n :: s[i] <= s[n]` */
method E(m: int, n: int, s: seq<int>) returns (m': int, n': int)
  // BEGIN-TODO(MethodE)
{
  // Declare local variables with arbitrary initial values
  var mm := m;
  var nn := n;

  // Final formulation of our weakest precondition
  assume n < |s| && forall i :: 0 <= i < nn ==> s[i] <= s[nn];

  // Perform the first assignment
  mm := nn;

  // Direct result of substitution for m := n
  assert forall i :: 0 <= i < nn ==> s[i] <= s[mm];

  // Perform the second assignment
  nn := nn + 1;

  // Check that the new state still satisfies the postcondition
  assert forall i :: 0 <= i < nn ==> s[i] <= s[mm];

  // Finally, assign to out-parameters
  m' := mm;
  n' := nn;
}
// END-TODO(MethodE)