// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// END-TODO(MethodA)


/* (e) WP(m := n; n := n + 1; forall i | 0 <= i < n :: s[i] <= s[m])
 * given that `forall i | 0 <= i < n :: s[i] <= s[n]` */
method E(m: int, n: int, s: seq<int>) returns (m': int, n': int)
// BEGIN-TODO(MethodE)
// Add the specification and the method body here.
// END-TODO(MethodE)