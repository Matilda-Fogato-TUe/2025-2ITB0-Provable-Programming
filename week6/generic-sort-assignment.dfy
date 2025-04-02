// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// Add the body of SplitPoint here
// END-TODO(SplitPoint)

ghost predicate transitive<T(!new)>(rel: (T, T) -> bool)
{
  forall a, b, c | rel(a, b) && rel(b, c) :: rel(a, c)
}

// BEGIN-TODO(Reflexivity)
// Add the reflexivity predicate here
// END-TODO(Reflexivity)

// BEGIN-TODO(Totality)
// Add the totality predicate here
// END-TODO(Totality)

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas
// END-TODO(Extra)

method SelectionSortGeneric<T(!new)>(a: array<T>, lte: (T, T) -> bool)
  modifies a
  ensures sorted(a, lte)
  ensures multiset(a[..]) == old(multiset(a[..]))
// BEGIN-TODO(SelectionSortGeneric)
// Add the body of the method SelectionSortGeneric here
// END-TODO(SelectionSortGeneric)

method TestStandard()
{
  var a := new int[3];
  a[0], a[1], a[2] := 2, 3, 1;
  assert a[..] == [2, 3, 1];
// BEGIN-TODO(TestStandard)
// Add your test cases here
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
// Add your test cases here, both for sorting on weight and sorting on price
// END-TODO(TestArticle)
}

