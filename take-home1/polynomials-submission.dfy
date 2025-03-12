// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
//
// Show us what you're made of!
//
// END-TODO(Name)

ghost function polyval(a: seq<int>, x: int): int
{
    if |a| == 0
    then
        0
    else
        var d := |a|-1; //degree, highest exponent of x
        polyval(a[..d], x) +a[d] * pow(x, d)
}


function pow(x: int, n: nat) : int
{
    if n == 0
    then
        1
    else
        x * pow(x, n - 1)
}


// BEGIN-TODO(Optional)
lemma polyval_slicing(a : seq<int>, x: int, i:nat)
    requires 0 < i <= |a|
    ensures polyval(a[..i], x) == polyval(a[..(i-1)], x) +a[i-1] * pow(x, i-1) 
{
    assert a[..i] == a[..(i-1)] + [a[i-1]];
    assert polyval(a[..i], x) == polyval(a[..(i-1)], x) +a[i-1] * pow(x, i-1);
    
}

function polyseg(a: seq<int>, x: int, lo: nat, hi: nat) : int
requires hi >= lo && hi <= |a|
decreases hi - lo
{
    if |a| == 0
    then 
        0
    else if lo == hi
    then 
        0
    else 
        polyseg(a, x, lo, hi - 1) + pow(x, hi - 1) * a[hi - 1]
}

lemma polyseg_equals_polyval_general(a: seq<int>, x:int, d: nat)
    requires 0 <= d <= |a|
    ensures polyval(a[..d], x) == polyseg(a, x, 0, d)
{
    if d == 0 {
        assert polyval(a[..d], x) == 0;
        assert polyseg(a[..d], x, 0, d) == 0;
    } else {
        var d' := d - 1;
        assert 0 <= d' <= |a|;
        polyval_slicing(a, x, d);
        assert polyval(a[..d], x) == polyval(a[..d'], x) + a[d'] * pow(x, d');
        assert polyseg(a, x, 0, d) == polyseg(a, x, 0, d') + pow(x, d') * a[d'];

        polyseg_equals_polyval_general(a, x, d');
        assert polyval(a[..d'], x) == polyseg(a, x, 0, d');
    }
}

lemma polyseg_equals_polyval(a: seq<int>, x:int)
    ensures polyval(a, x) == polyseg(a, x, 0, |a|)
{
    polyseg_equals_polyval_general(a, x, |a|);
    assert polyval(a[..|a|], x) == polyseg(a, x, 0, |a|);
    assert a[..|a|] == a;
}
// END-TODO(Optional)


method polySimple(a: seq<int>, x: int) returns (r: int)
    ensures r == polyval(a, x)
// BEGIN-TODO(NaivePoly)
{
    var i := 0;
    r := 0;
    while (i < |a|) 
        invariant 0 <= i <= |a|
        invariant r == polyval(a[..i], x)
    {
        r := r + a[i] * pow(x, i);
        i := i + 1;
        polyval_slicing(a, x, i);
        assert polyval(a[..i], x) == polyval(a[..(i-1)], x) +a[i-1] * pow(x, i-1);
        assert r == polyval(a[..i], x);
    }
    assert i == |a|;
    assert a == a[..|a|];
    assert r == polyval(a, x);
}
// END-TODO(NaivePoly)


method polyPowerCache(a: seq<int>, x: int) returns (r: int)
    ensures r == polyval(a, x)
// BEGIN-TODO(CachePoly)
{
    var i := 0;
    r := 0;
    var power_x := 1;
    while (i < |a|) 
        invariant 0 <= i <= |a|
        invariant r == polyval(a[..i], x)
        invariant power_x == pow(x, i)
    {
        r := r + a[i] * power_x;
        i := i + 1;
        power_x := power_x * x;
        polyval_slicing(a, x, i);
        assert polyval(a[..i], x) == polyval(a[..(i-1)], x) +a[i-1] * pow(x, i-1);
        assert r == polyval(a[..i], x);
    }
    assert i == |a|;
    assert a == a[..|a|];
    assert r == polyval(a, x);
}
// END-TODO(CachePoly)


method Horner(a: seq<int>, x: int) returns (r: int)
    ensures r == polyval(a, x)
// BEGIN-TODO(HornerPoly)
// Implement Horner's scheme for calculating the value of a polynomial.
// END-TODO(HornerPoly)
