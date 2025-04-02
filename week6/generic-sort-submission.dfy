// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

datatype Article = Article(name: string, weight: real, price: int)

predicate standardOrdering(a: int, b: int)
{ 
  a <= b
}

ghost predicate sorted<T>(a: array<T>, lte: (T, T) -> bool)
  reads a
{ 
  forall i, j :: 0 <= i < j < a.Length ==> lte(a[i], a[j])
}

ghost predicate SplitPoint<T>(a: array<T>, lte: (T, T) -> bool, n: int)
// BEGIN-TODO(SplitPoint)
reads a
{
  forall i, j :: 0 <= i < n <= j < a.Length ==> lte(a[i], a[j])
}
// END-TODO(SplitPoint)

ghost predicate transitive<T(!new)>(rel: (T, T) -> bool)
{
  forall a, b, c | rel(a, b) && rel(b, c) :: rel(a, c)
}

// BEGIN-TODO(Reflexivity)
ghost predicate reflexive<T(!new)>(rel: (T, T) -> bool)
{
  forall a :: rel(a, a)
}
// END-TODO(Reflexivity)

// BEGIN-TODO(Totality)
ghost predicate total<T(!new)>(rel: (T, T) -> bool)
{
  forall a, b :: rel(a, b) || rel(b, a)
}
// END-TODO(Totality)

// BEGIN-TODO(Extra)
predicate weightOrdering(a: Article, b: Article)
{
  a.weight <= b.weight
}

predicate priceInverseOrdering(a: Article, b: Article)
{
  a.price >= b.price
}
// END-TODO(Extra)

method SelectionSortGeneric<T(!new)>(a: array<T>, lte: (T, T) -> bool)
  modifies a
  ensures sorted(a, lte)
  ensures multiset(a[..]) == old(multiset(a[..]))
// BEGIN-TODO(SelectionSortGeneric)
  requires transitive(lte) && reflexive(lte) && total(lte)
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> lte(a[i], a[j])
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant SplitPoint(a, lte, n)
  {
    var mindex, m := n, n+1;
    while m != a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> lte(a[mindex], a[i])
    {
      if lte(a[m], a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
}
// END-TODO(SelectionSortGeneric)

method TestStandard()
{
  var a := new int[3];
  a[0], a[1], a[2] := 2, 3, 1;
  assert a[..] == [2, 3, 1];
// BEGIN-TODO(TestStandard)
  SelectionSortGeneric(a, standardOrdering);
  assert a[..] == [1, 2, 3];
// END-TODO(TestStandard)
}

method TestArticle()
{
  var a := new Article[3];
  var x := Article("x", 2.0, 10);
  var y := Article("y", 3.0, 11);
  var z := Article("z", 1.0, 12);
  a[0] := x; a[1] := y; a[2] := z;

// BEGIN-TODO(TestArticle)
  assert a[..] == [x, y, z];
  //sort on weight
  SelectionSortGeneric(a, weightOrdering);
  assert a[..] == [z, x, y];
  //sort on price, highest first
  SelectionSortGeneric(a, priceInverseOrdering);
  assert a[..] == [z, y, x];
// END-TODO(TestArticle)
}

