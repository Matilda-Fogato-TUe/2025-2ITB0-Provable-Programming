// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

method ReverseArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
{
  // BEGIN-TODO(IsCelebrity)
  var i := 0;
  var j := a.Length - 1;
  while i < j
    decreases j - i
    invariant 0 <= i <= a.Length
    invariant -1 <= j < a.Length
    invariant j == a.Length - 1 - i
    // The part of the array before i is already in its final reversed state
    invariant forall k | 0 <= k < i :: a[k] == old(a[a.Length - 1 - k])
    // The part of the array after j is already in its final reversed state
    invariant forall k | j < k < a.Length :: a[k] == old(a[a.Length - 1 - k])
    // Do not swap elements that are between i and j
    invariant forall k | i <= k <= j :: a[k] == old(a[k])
  {
    var tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
  // END-TODO(IsCelebrity)
}
