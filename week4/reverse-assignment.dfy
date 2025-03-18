// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
//
// Good luck!
//
// END-TODO(Name)

method ReverseArray(a: array<int>) 
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
{
// BEGIN-TODO(IsCelebrity)
// Implement the method `ReverseArray`
// END-TODO(IsCelebrity)
}

