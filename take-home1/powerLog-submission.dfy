// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Show us what you're made of!
//
// END-TODO(Name)

ghost function pow(x: nat, n: nat): nat
{
  if n == 0 then 1 else x * pow(x, n - 1)
}

// BEGIN-TODO(Optional)
// Optionally add your lemmas and helper functions here.
lemma {:induction false} PowEven(x: nat, n: nat)
  requires n > 0 && n % 2 == 0
  ensures pow(x, n) == pow(x * x, n / 2)
{
  if n == 2 {
    assert pow(x, 2) == x * pow(x, 1) == x * x == pow(x * x, 1);
  } else {
    //PowEven(x, n - 2);
    calc {
      pow(x, n);
    ==
      x * pow(x, n - 1); // Apply definition of pow
    ==
      x * (x * pow(x, n -2));
    ==
      x * x * pow(x, n - 2);
    == {// Induction hypothesis
         PowEven(x, n - 2);
         assert pow(x, n - 2) == pow(x * x, (n - 2) / 2);
       }
      x * x * pow(x * x, (n - 2) / 2); // Apply induction hypothesis
    ==
      pow(x * x, n / 2); // Note that (n-2)/2 == (n/2) - 1
    }
  }
}

lemma {:induction false} PowOdd(x: nat, n: nat)
  requires n > 0 && n % 2 == 1
  ensures pow(x, n) == x * pow(x * x, n / 2)
{
  if n == 1 {
    assert pow(x, 1) == x == x * pow(x * x, 0);
  } else {
    //PowOdd(x, n - 2);
    calc {
      pow(x, n);
    ==
      x * pow(x, n - 1); // Apply definition of pow
    ==
      x * (x * pow(x, n - 2));
    ==
      x * x * pow(x, n - 2);
    == {// Induction hypothesis
         PowOdd(x, n - 2);
         assert pow(x, n - 2) == x * pow(x * x, (n - 2) / 2);
       }
      x * x * x * pow(x * x, (n - 2) / 2); // Apply induction hypothesis
    ==
      x * pow(x * x, n / 2); // Note that (n-2)/2 == (n/2) - 1
    }
  }
}
// END-TODO(Optional)

method FastExp(X: nat, N: nat) returns (y: nat)
  ensures y == pow(X, N)
  // BEGIN-TODO(FastExp)
  // Give a verifying implementation of log-time exponentiation that follows the
  // specification given in `pow`.
{
  y := 1;
  var x := X;
  var n := N;
  while n != 0
    invariant y * pow(x, n) == pow(X, N)
  {
    if n % 2 == 1 {
      PowOdd(x, n);
      y := y * x;
      n := n / 2;
      x := x * x;
    } else {
      PowEven(x, n);
      n := n / 2;
      x := x * x;
    }
  }
}
// END-TODO(FastExp)

