// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
//
// Go get 'em!
//
// END-TODO(Name)

predicate isOdd(m: int)
{
  m % 2 == 1
}

/* (a) Obtain a head invariant by replacing a constant in the postcondition by a
 * variable and implement the method. */
method OddityHead(s: seq<int>) returns (b: bool)
    ensures b <==> forall i | 0 <= i < |s| :: isOdd(s[i])
{
// BEGIN-TODO(HeadInv)
// Write an implementation for this method using a loop with a so-called head
// invariant, which Leino refers to in his loop design technique 12.0.
// END-TODO(HeadInv)
}


/* (b) Implement this method again using a tail invariant of the shape
 * (forall i | 0 <= i < |s| :: isOdd(s[i]) <==> ...) */
method OddityTail(s: seq<int>) returns (b: bool)
    ensures b <==> forall i | 0 <= i < |s| :: isOdd(s[i])
{
// BEGIN-TODO(TailInv)
// Write an implementation for this method using a loop with a so-called tail
// invariant, which Leino refers to in his loop design technique 12.1.
// END-TODO(TailInv)
}