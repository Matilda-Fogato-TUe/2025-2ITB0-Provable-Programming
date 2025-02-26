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
  // WP [x := 3y - 2x, x <= y] = WP [y <=x]
  //requires y <= x
  //ensures x' <= y
{
  assume y <= x;
  x' := 3*y - 2*x;
  assert x' <=y;
}

// END-TODO(MethodA)


/* (e) WP(m := n; n := n + 1; forall i | 0 <= i < n :: s[i] <= s[m])
 * given that `forall i | 0 <= i < n :: s[i] <= s[n]` */
method E(m: int, n: int, s: seq<int>) returns (m': int, n': int)
  // BEGIN-TODO(MethodE)
{
  //assumptions required for 'given that' to be true.
  n':= n;
  m':= m;

  assume n' < |s|;
  assume forall i | 0 <= i < n :: s[i] <= s[n'];

  m' := n';
  assert forall i | 0 <= i < n' :: s[i] <= s[m'];
  n' := n' + 1;
  assert forall i | 0 <= i < n' :: s[i] <= s[m'];
}
// END-TODO(MethodE)