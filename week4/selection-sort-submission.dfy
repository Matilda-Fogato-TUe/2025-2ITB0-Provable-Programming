// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// You got this!!
//
// END-TODO(Name)

method SelectionSortAlternative(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant SplitPoint(a, n)
  {
    var m := n + 1;
    while m != a.Length
      // BEGIN-TODO(inner-loop)
      // use in the loop the following statement
      // a[n], a[m] := a[m], a[n];
      decreases a.Length - m
      invariant n < m <= a.Length
      invariant forall k :: n <= k < m ==> a[n] <= a[k]
      invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant SplitPoint(a, n)
    {
      if a[m] < a[n] {
        // Swap a[n] and a[m] as soon as a new minimum is found.
        a[n], a[m] := a[m], a[n];
      }
      m := m + 1;
    }
    // END-TODO(inner-loop)
    n := n + 1;
  }
}

ghost predicate SplitPoint(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

