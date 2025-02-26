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
// loop-use: YES
// assertion: NO
// END-TODO(TestB)


/* (c)
 * x := 20;
 * while x < 20
 *     invariant x % 2 == 0
 * assert x == 20; */
method TestC()
// BEGIN-TODO(TestC)
// loop-use: YES
// assertion: NO
// END-TODO(TestC)


/* (g)
 * x := 0;
 * while x < 100
 *     invariant 0 <= x < 100
 * assert x == 25; */
method TestG()
  // BEGIN-TODO(TestG)
  // loop-use: YES
  // assertion: NO
// END-TODO(TestG)