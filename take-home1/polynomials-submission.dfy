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

lemma PowProperty(x: int, a: nat, b:nat) 
    requires b >= a
    ensures pow(x, b) == pow(x, a) * pow(x, b - a)
{
    if b == a {
        assert pow(x, b - a) == 1;
        assert pow(x, b) == pow(x, a);
        assert pow(x, b) == pow(x, a) * pow(x, b - a);
    } else {
        calc {
            pow(x, b);
            == //Def. pow for n := b
            x * pow(x, b - 1);
            == {PowProperty(x, a, b-1);}
            x * (pow(x, a) * pow(x, b - a - 1));
            == //Rearrange
            pow(x, a) * x * pow(x, b - a - 1);
            == //Def. pow for n := b - 1
            pow(x, a) * pow(x, b - a);
        }
    }
}

lemma polyval_double_slicing(a: seq<int>, x:int, i:nat, j: nat) 
    requires 0 <= i < j <= |a|
    ensures polyval(a[i..j], x) == polyval(a[i..j-1], x) + a[j-1] * pow(x, j-i-1)
{
    // Step 1: Show that a[i..j] is the concatenation of a[i..j-1] and [a[j-1]]
    assert a[i..j] == a[i..j-1] + [a[j-1]];

    // Step 2: Apply the definition of polyval to a[i..j]
    var d := |a[i..j]| - 1; // Degree of the polynomial
    assert d == j - i - 1; // Since |a[i..j]| = j - i

    // Step 3: Expand polyval(a[i..j], x) using its definition
    assert polyval(a[i..j], x) == polyval(a[i..j-1], x) + a[j-1] * pow(x, d);

    // Step 4: Substitute d = j - i - 1
    assert polyval(a[i..j], x) == polyval(a[i..j-1], x) + a[j-1] * pow(x, j-i-1);

}

function polyseg(a: seq<int>, x: int, lo: nat, hi: nat): int
  requires hi <= |a| && |a| > lo >= 0 && lo < hi // Ensure hi is within bounds
  ensures polyseg(a, x, lo, hi) == pow(x, lo) * polyval(a[lo..hi], x) // Postcondition
{
  if lo >= hi-1 then
    var res := a[lo] * pow(x, lo);
    res
  else 
    var r := polyseg(a, x, lo, hi-1);
    var res := r + a[hi-1] * pow(x, hi-1);
    calc{
        res;
        == //Def. res
        r + a[hi-1] * pow(x, hi-1);
        == //Def. r
        polyval(a[lo..hi-1], x) * pow(x, lo) + a[hi-1] * pow(x, hi-1);
        == {PowProperty(x, lo, hi - 1);}
        pow(x, lo) * (polyval(a[lo..hi-1], x) + a[hi-1] * pow(x, hi-lo-1));
        == {polyval_double_slicing(a, x, lo, hi);}
        pow(x, lo) * polyval(a[lo..hi], x);
    }
    res
}

lemma polyseg_Equals_Polyval(a: seq<int>, x:int) 
    requires |a| > 0
    ensures polyseg(a, x, 0, |a|) == polyval(a, x)
{
    assert polyseg(a, x, 0, |a|) == polyval(a, x);
}

lemma polyseg_decomposition(a: seq<int>, x: int, lo: nat, hi: nat)
  requires hi <= |a| && |a| > lo >= 0 && lo < hi - 1 // Ensure hi is within bounds
  ensures polyseg(a, x, lo, hi) == a[lo] * pow(x, lo) + polyseg(a, x, lo+1, hi)
{
    if lo == hi - 2 {
        assert hi == lo + 2;
        assert polyseg(a, x, lo, lo+2) == a[lo] * pow(x, lo) + polyseg(a, x, lo+1, lo+2);
    } else {
        calc {
            polyseg(a, x, lo, hi);
            == //Def. polyseg
            polyseg(a, x, lo, hi-1) + a[hi-1] * pow(x, hi-1);
            == {polyseg_decomposition(a, x, lo, hi - 1);}
            a[lo] * pow(x, lo) + polyseg(a, x, lo+1, hi - 1) + a[hi-1] * pow(x, hi-1);
            ==
            a[lo] * pow(x, lo) + polyseg(a, x, lo+1, hi);
        }
    }
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
{
    if |a| == 0 {
        r := 0;
    } else {
        var i := |a|-1;
        r := a[i];
        while i > 0 
            invariant 0 <= i < |a|
            invariant r * pow(x, i) == polyseg(a, x, i, |a|)
            decreases i
        {
            //keep old variable to prove maintenance more easily
            var r_old := r;

            i := i - 1;
            r := a[i] + x * r;
            
            //proof maintenance
            calc {
                r * pow(x, i);
                ==
                (a[i] + x * r_old) * pow(x, i);
                ==
                a[i] * pow(x, i) + x * pow(x, i) * r_old;
                == {assert pow(x, i + 1) * r_old == polyseg(a, x, i + 1, |a|);}
                a[i] * pow(x, i) + polyseg(a, x, i + 1, |a|);
                == {polyseg_decomposition(a, x, i, |a|);}
                polyseg(a, x, i, |a|);
            }
        }
    }
}
// END-TODO(HornerPoly)
