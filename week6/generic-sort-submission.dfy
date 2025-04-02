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
  requires 0 <= n <= a.Length
{
  // Every element in the left partition is less than or equal to every element in the right partition.
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
ghost predicate totality<T(!new)>(rel: (T, T) -> bool)
{
  // For any two distinct elements, either one is less than the other or vice versa.
  forall a, b | a != b :: rel(a, b) || rel(b, a)
}
// END-TODO(Totality)

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas
predicate articleWeightOrdering(a1: Article, a2: Article)
{
  a1.weight <= a2.weight
}

predicate articlePriceOrdering(a1: Article, a2: Article)
{
  a1.price >= a2.price
}
// END-TODO(Extra)

method SelectionSortGeneric<T(!new)>(a: array<T>, lte: (T, T) -> bool)
  modifies a
  ensures sorted(a, lte)
  ensures multiset(a[..]) == old(multiset(a[..]))
  // BEGIN-TODO(SelectionSortGeneric)
  requires reflexive<T>(lte)
  requires transitive<T>(lte)
  requires totality<T>(lte)
  // Add the body of the method SelectionSortGeneric here
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> lte(a[i], a[j])
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant SplitPoint(a, lte, n)
  {
    var mindex, m := n, n + 1;
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
    assert forall i, j :: 0 <= i < j < n ==> lte(a[i], a[j]);
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
  // Add your test cases here
  SelectionSortGeneric<int>(a, standardOrdering);
  assert sorted(a, standardOrdering);
  assert a[..] == [1, 2, 3];
  assert multiset(a[..]) == multiset([2, 3, 1]);
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

  // Sort the array on weight
  SelectionSortGeneric<Article>(a, articleWeightOrdering);
  assert sorted(a, articleWeightOrdering);
  assert a[0].weight <= a[1].weight && a[1].weight <= a[2].weight;
  assert a[..] == [z, x, y];
  assert multiset(a[..]) == multiset([z, x, y]);

  // Sort the array on price
  SelectionSortGeneric<Article>(a, articlePriceOrdering);
  assert sorted(a, articlePriceOrdering);
  assert a[0].price >= a[1].price && a[1].price >= a[2].price;
  assert a[..] == [z, y, x];
  assert multiset(a[..]) == multiset([z, y, x]);
  // END-TODO(TestArticle)
}

