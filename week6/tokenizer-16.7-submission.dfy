// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

/* == Book exercise 16.7 ==
 * As written, Tokenizer holds on to the given string forever. Change the design
 * to make it possible to prune the storage through a method that throws away
 * the prefix of the source string that has already been processed.
 * Specifically, make source a ghost and declare a mutable field suffix with the
 * invariant suffix == source[m..], where m is a new field. For example, you can
 * introduce fields m and j such that m + j == n, in which case you can declare
 * n as ghost as well. Modify the implementation of Read accordingly. */

datatype Category = Identifier | Number | Operator | Whitespace | Error | End

predicate Is(ch: char, cat: Category)
  requires cat != End
  decreases cat == Error
{
  match cat
  case Whitespace => ch in " \t\r\n"
  case Identifier => 'A' <= ch <= 'Z' || 'a' <= ch <= 'z'
  case Number => '0' <= ch <= '9'
  case Operator => ch in "+-*/%!=><~^&|"
  case Error => !Is(ch, Identifier) && !Is(ch, Number) &&
                !Is(ch, Operator) && !Is(ch, Whitespace)
}

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas (optional)

// END-TODO(Extra)

class Tokenizer {
  // BEGIN-TODO(Attributes)
  ghost var source: string
  var suffix: string
  var m: nat  // the index in source where suffix begins
  var j: nat // such that n = m + j, j represents the length processed within the suffix
  ghost var n: nat  // n is ghost and equals m+j
  // END-TODO(Attributes)

  ghost predicate Valid()
    reads this
  {
    // BEGIN-TODO(Invariant)
    // The invariant expresses that suffix is the unprocessed part of source starting at m
    // and that n is the total number of characters processed (n = m+j).
    0 <= m <= |source|
    && 0 <= j <= |suffix|
    && n <= |source|
    && suffix == source[m..]
    && n == m + j
    && source == source[..m] + suffix
    // END-TODO(Invariant)
  }

  constructor (s: string)
    ensures Valid() && source == s && n == 0
  {
    // BEGIN-TODO(Constructor)
    source := s;
    suffix := s;
    m := 0;
    j := 0;
    n := 0;
    // END-TODO(Constructor)
  }

  method Read() returns (cat: Category, ghost p: nat, token: string)
    requires Valid()
    modifies this
    ensures cat == End || cat == Error || Valid()
    ensures cat != Whitespace
    ensures old(n) <= p <= n <= |source|
    ensures cat == End <==> p == |source|
    ensures cat == End || cat == Error <==> p == n
    ensures forall i :: old(n) <= i < p ==> Is(source[i], Whitespace)
    ensures forall i :: p <= i < n ==> Is(source[i], cat)
    ensures p < n ==> n == |source| || !Is(source[n], cat)
    ensures token == source[p..n]
  {
    // BEGIN-TODO(Read)

    ghost var oldN := n;
    assert n == m + j;


    // skip whitespace
    while j < |suffix| && Is(suffix[j], Whitespace)
      invariant Valid()
      invariant old(j) <= j <= |suffix|
      invariant forall i :: old(j) <= i < j ==> Is(suffix[i], Whitespace)
      invariant forall i :: old(n) <= i < m + j ==> Is(source[i], Whitespace)
      invariant n == m + j && m <= |source|
      invariant suffix == source[m..]
      invariant old(m) == m
    {
      j := j + 1;
      n := m + j;
    }

    // set p to the position after the whitespace
    p := j + m;

    assert oldN == old(n);
    assert p == n;
    assert IsWhitespaceRange(oldN, p);

    // Establish and save the whitespace property here, close to where it was proven
    ghost var allWhitespaceBeforeP := forall i :: old(n) <= i < p ==> Is(source[i], Whitespace);
    assert allWhitespaceBeforeP;

    // check for end of string
    if j == |suffix| {
      assert suffix == source[m..];
      assert p == j + m;
      assert |suffix| == |source| - m;
      assert j == |suffix| ==> j + m == |source|;
      assert p == n;
      assert p == |source|;
      cat := End;
      token := "";
      assert IsWhitespaceRange(oldN, p);
      assert allWhitespaceBeforeP;
      return;
    }

    // determine syntactic category
    var ch := suffix[j];
    if Is(ch, Identifier) {
      cat := Identifier;
    } else if Is(ch, Number) {
      cat := Number;
    } else if Is(ch, Operator) {
      cat := Operator;
    } else {
      cat := Error;
      token := "";
      assert p == n == m + j;
      assert IsWhitespaceRange(oldN, p);
      assert allWhitespaceBeforeP;
      assert token == source[p..n];
      return;
    }

    // read all consecutive characters of the same category
    var start := j;
    j := j + 1;
    n := n + 1;

    assert j == start + 1;
    assert start < j;
    assert suffix[start] == ch;  // The first character is of the right category
    assert Is(suffix[start], cat);  // Explicit about the category
    assert p == start + m;  // Connect p to start
    assert m + start < m + j;  // Help relate positions
    assert p < n;  // Explicit about p being less than n

    while j < |suffix| && Is(suffix[j], cat)
      invariant Valid()
      invariant p - m <= j <= |suffix|
      invariant forall i :: start <= i < j ==> Is(suffix[i], cat)
      invariant forall i :: p <= i < m + j ==> Is(source[i], cat)
      invariant n == m + j
      invariant p == start + m
      invariant suffix == source[m..]
      invariant start < j
    {
      j := j + 1;
      n := m + j;
    }

    // extract the token
    token := suffix[start..j];
    assert p == start + m;
    assert n == j + m;
    assert source[p..n] == suffix[start..j];
    assert token == source[p..n];
    assert start < j;  // This is true because we've processed at least one character
    assert p < n;  // This follows from the previous assertions
    assert cat != Whitespace;  // This is true because we are not in the whitespace case
    assert cat != End && cat != Error;  // This is true in the normal case
    assert (cat == End || cat == Error) <==> p == n;  // This confirms the biconditional
    if j < |suffix| {
      assert !Is(suffix[j], cat);
      assert source[n] == suffix[j];
      assert !Is(source[n], cat);
    } else {
      assert j == |suffix|;  // This is true because we've processed all characters
      assert n == |source|;
      assert suffix == source[m..];
      assert m + j == |source|;  // This confirms the end of the string
    }
    assert allWhitespaceBeforeP;

    // Verify all ensures clauses are satisfied
    assert cat == End || cat == Error || Valid();
    assert cat != Whitespace;
    assert old(n) <= p <= n <= |source|;
    assert cat == End <==> p == |source|;
    assert cat == End || cat == Error <==> p == n;
    assert allWhitespaceBeforeP;
    assert forall i :: p <= i < n ==> Is(source[i], cat);
    assert p < n ==> (n == |source| || !Is(source[n], cat));
    assert token == source[p..n];

    // END-TODO(Read)
  }

  method Prune()
    requires Valid()
    modifies this
    ensures Valid() && source == old(source[m..]) == suffix
  {
    // BEGIN-TODO(Prune)
    ghost var oldSource := source;
    ghost var oldM := m;
    assert suffix == source[m..];
    source := suffix;
    var oldJ := j;
    m := 0;
    n := j;
    assert source == oldSource[oldM..];
    assert suffix == source;
    assert Valid();
    // END-TODO(Prune)
  }

  // BEGIN-TODO(Methods)
  ghost predicate IsWhitespaceRange(start: nat, end: nat)
    requires start <= end
    requires end <= |source|
    reads this
  {
    forall i {:trigger source[i]} :: start <= i < end ==> Is(source[i], Whitespace)
  }
  // END-TODO(Methods)
}