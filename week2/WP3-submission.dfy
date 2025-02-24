// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// You got this!!
//
// END-TODO(Name)



/* == Book exercise 2.21 ==
 * Compute the weakest precondition for the following statement with respect to
 * `y < 10`. Simplify the condition.
 *
 *  if x < 8 {
 *      if x == 5 {
 *          y := 10;
 *      } else {
 *          y := 2;
 *       }
 *  } else {
 *      y := 0;
 *  } */
method Ex(x: int, y: int) returns (y': int)
  // BEGIN-TODO(Method)
  // Add the specification and the method body here.
  requires x < 8 && x != 5
  ensures y' < 10
{
  if x < 8 {
    if x == 5 {
      y' := 10;
    } else {
      y' := 2;
    }
  } else {
    y' := 0;
  }
}
// END-TODO(Method)