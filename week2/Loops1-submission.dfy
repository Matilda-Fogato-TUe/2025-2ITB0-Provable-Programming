// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// You got this!!
//
// END-TODO(Name)



/* == Book exercise 11.0 ==
 * For each of the following uses of loop specifications, indicate whether or
 * not the loop-use proof obligation is met and whether or not the assertion
 * following the loop can be proved to hold. */

/* (b)
 * x := 20;
 * while 10 < x
 *     invariant x % 2 == 0
 * assert x == 10; */
method TestB()
  // BEGIN-TODO(TestB)
  // Add the specification and the method body here.
  // The loop-use proof obligation that x % 2 == 0 holds on entry is provable (x == 20 on entry)
  // The assertion is not provable: in order to conclude that x == 10 after the loop,
  // the negation of the guard is x <= 10, and the invariant should stipulate that x >= 10.
{
  var x := 20;
  while 10 < x
    invariant x % 2 == 0
    decreases x
  {
    //{{x % 2 ==0 && 10 < x}}
    x := x - 2;
    // {{x % 2 == 0}}
  }
  assert x == 10;
}

// END-TODO(TestB)


/* (c)
 * x := 20;
 * while x < 20
 *     invariant x % 2 == 0
 * assert x == 20; */
method TestC()
  // BEGIN-TODO(TestC)
  // Add the specification and the method body here.
  // The loop-use proof obligation that x % 2 == 0 holds on entry is provable (x == 20 on entry)
  // To prove the assertion, we need to prove x % 2 == 0 && x >= 20 ==> x == 20.
  // We cannot prove this implication.
{
  var x := 20;
  while x < 20
    invariant x % 2 == 0
  {
    // {{x % 2 == 0 && x < 20}}
    x := x + 2;
    // {{x % 2 == 0}}
  }
  assert x == 20;
}
// END-TODO(TestC)


/* (g)
 * x := 0;
 * while x < 100
 *     invariant 0 <= x < 100
 * assert x == 25; */
method TestG()
  // BEGIN-TODO(TestG)
  // Add the specification and the method body here.
  // The loop-use proof obligation that 0 <= x < 100 holds on entry is provable (x == 0 on entry)
  // To prove the assertion, we need to prove 0 <= x < 100 && x >= 100 ==> x == 25.
  // We cannot prove this implication.
{
  var x := 0;
  while x < 100
    invariant 0 <= x < 100
  {
    // {{0 <= x < 100 && x < 100}}
    //x := x;
    // {{0 <= x <100}}
  }
  assert x == 25;
}

// END-TODO(TestG)