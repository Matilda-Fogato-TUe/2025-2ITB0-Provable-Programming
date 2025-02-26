// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// You got this!!
//
// END-TODO(Name)



/* == Book exercise 11.6 ==
 * Consider the following program fragment:
 *
 * x := 0;
 * while x < 100
 * {
 *     x := x + 3;
 * }
 * assert x == 102;
 *
 * Write a loop invariant that holds initially, is maintained by the loop body,
 * and allows you to prove the assertion after the loop. */
method Solution()
  // BEGIN-TODO(Solution)
{
  var x := 0;
  while x < 100
    invariant x % 3 == 0
    invariant x <= 102
  {
    x := x + 3;
  }
  assert x == 102;
}
// END-TODO(Solution)