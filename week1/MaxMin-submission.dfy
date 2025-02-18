// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Jip Melle Verkoulen: 1836587
// Matilda Fogato: 1656376
// END-TODO(Name)



/* == Handout exercise 1.9 ==
 * The methods `Max` and `Negate` are not implemented. Nevertheless, we can
 * write code that calls them and prove this code correct, using the contracts
 * of these methods. Implement the method `Min` and make sure it verifies. */
method {:axiom} Negate(a: seq<int>) returns (nega: seq<int>)
  ensures |nega| == |a|
  ensures forall i | 0 <= i < |a| :: nega[i] == -a[i]

method {:axiom} Max(a: seq<int>) returns (max: int)
  requires |a| > 0
  ensures max in a
  ensures forall i | 0 <= i < |a| :: a[i] <= max

method Min(a: seq<int>) returns (min: int)
  requires |a| > 0
  ensures min in a
  ensures forall i | 0 <= i < |a| :: min <= a[i]
  // BEGIN-TODO(Implementation)
  // Add your implementation here.
{
  // Negate the sequence
  var nega := Negate(a);
  // Find the maximum of the negated sequence
  var max := Max(nega);
  // Negate the maximum to find the minimum
  min := -max;
  // Assert that the minimum is in the sequence
  assert min in a;
  // Assert that the minimum is less than or equal to all elements in the sequence
  assert forall i | 0 <= i < |a| :: min <= a[i];
}
// END-TODO(Implementation)
