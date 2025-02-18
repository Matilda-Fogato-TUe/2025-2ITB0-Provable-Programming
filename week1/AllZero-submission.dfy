// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Jip Melle Verkoulen: 1836587
// Matilda Fogato: 1656376
// Group number 36
// END-TODO(Name)



/* == Handout question 1.3 ==
 * Consider a method
 * `method AllZero(a: seq<int>) returns (r: bool)`
 * that calculates whether all elements of sequence `a` are zero. */

/* (a) Specify this method. Note that of an empty sequence all elements are
 * zero. */

/* (b) Test this specification with at least four cases, two `true` and two
 * `false`. Note that Dafny needs a witness in order to be able to prove that a
 * forall-formula does not hold. */

/* (c) Implement this method recursively and make sure that it verifies. Note
 * that Dafny does not allow method calls directly in expressions. To use the
 * result of a method call in an expression, first assign the result to a
 * variable and then use this variable in the expression. */


method AllZero(a: seq<int>) returns (r: bool)
// BEGIN-TODO(Method)
// Add the specification and the method body here.
  ensures r == (forall i :: 0 <= i < |a| ==> a[i] == 0)
  decreases |a|
{
  if |a| == 0 {
    r := true;
  } else {
    var rest := AllZero(a[1..]);
    //assert rest <==> (forall i :: 0 <= i < |a[1..]| ==> a[1..][i] == 0);
    r := a[0] == 0 && rest;

  }
  assert r == (forall i :: 0 <= i < |a| ==> a[i] == 0);
}
// END-TODO(Method)

// BEGIN-TODO(Test)
// Add your test cases here.
method TestAllZero()
{
  var r := AllZero([]);
  assert r == true;

  var s := AllZero([1]);
  assert 0 <= 0 < |[1]| && [1][0] != 0;
  assert s == false;

  var t := AllZero([0, 0]);
  assert t == true;

  var u := AllZero([1, 1, 1]);
  assert 0 <= 0 < |[1, 1, 1]| && [1, 1, 1][0] != 0;
  assert u == false;
}
// END-TODO(Test)
