// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// END-TODO(Implementation)
