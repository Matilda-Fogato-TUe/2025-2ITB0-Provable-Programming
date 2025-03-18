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
var i: int := 0;
    var j: int := a.Length - 1;
    while i < j
        invariant 0 <= i <= j + 1 <= a.Length
        invariant j == a.Length - 1 - i
        invariant forall k | 0 <= k < i :: a[k] == old(a[a.Length - 1 - k])
        invariant forall k | j < k < a.Length :: a[k] == old(a[a.Length - 1 - k])
        invariant forall k | i <= k <= j :: a[k] == old(a[k])
    {
        var temp := a[i];
        a[i] := a[j];
        a[j] := temp;

        i := i + 1;
        j := j - 1;

        //asserts not required but added for understandability
        assert forall k | 0 <= k < i - 1 :: a[k] == old(a[a.Length - 1 - k]); //start of body
        assert a[i - 1] == old(a[j + 1]);
        assert a[i - 1] == old(a[a.Length - i]);
        assert forall k | 0 <= k < i :: a[k] == old(a[a.Length - 1 - k]);

        assert forall k | j + 1 < k < a.Length :: a[k] == old(a[a.Length - 1 - k]);
        assert a[j + 1] == old(a[i - 1]);
        assert a[j + 1] == old(a[a.Length - 2 - j]);
        assert forall k | j < k < a.Length :: a[k] == old(a[a.Length - 1 - k]);
    }
// END-TODO(IsCelebrity)
}
