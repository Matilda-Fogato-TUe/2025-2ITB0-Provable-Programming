// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
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
  var n := 0;
  b := true;
  while n != |s|
    invariant 0 <= n <= |s|
    invariant b <==> forall i | 0 <= i < n :: isOdd(s[i])
  {
    b := b && isOdd(s[n]);
    n := n + 1;
  }
  assert b <==> forall i | 0 <= i < |s| :: isOdd(s[i]);
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
  var n := 0;
  b := true;
  while n < |s|
    invariant 0 <= n <= |s|
    invariant (forall i | 0 <= i < |s| :: isOdd(s[i])) <==> (b && (forall j | n <= j < |s| :: isOdd(s[j])))
  {
    b := b && isOdd(s[n]);
    n := n + 1;
  }
  // END-TODO(TailInv)
}