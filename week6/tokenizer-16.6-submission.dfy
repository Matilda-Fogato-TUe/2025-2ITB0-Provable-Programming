// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

/* == Book exercise 16.6 ==
 * Extend the Tokenizer example to treat the first character of a token
 * differently. Specifically, replace predicate Is with two predicates:
 * IsStart(ch, cat) says whether or not character ch is a legal initial
 * character of category cat, and IsFollow(ch, cat) says whether or not ch is a
 * legal non-initial character of cat. Use these to allow Identifier to start
 * with a letter and to continue with any letters and digits. Then, update the
 * specification and implementation of method Read(). */

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

// BEGIN-TODO(MethodsAndMore)
// Space for the required Is___ methods and other additions
predicate IsStart(ch: char, cat: Category)
  requires cat != End
  decreases cat == Error
{
  match cat
  case Whitespace => ch in " \t\r\n"
  case Identifier => 'A' <= ch <= 'Z' || 'a' <= ch <= 'z'
  case Number => '0' <= ch <= '9'
  case Operator => ch in "+-*/%!=><~^&|"
  case Error => !IsStart(ch, Identifier)
                && !IsStart(ch, Number)
                && !IsStart(ch, Operator)
                && !IsStart(ch, Whitespace)
}

predicate IsFollow(ch: char, cat: Category)
  requires cat != End
  decreases cat == Error
{
  match cat
  case Whitespace => ch in " \t\r\n"
  case Identifier => 'A' <= ch <= 'Z' || 'a' <= ch <= 'z' || '0' <= ch <= '9'
  case Number => '0' <= ch <= '9'
  case Operator => ch in "+-*/%!=><~^&|"
  case Error => !IsFollow(ch, Identifier)
                && !IsFollow(ch, Number)
                && !IsFollow(ch, Operator)
                && !IsFollow(ch, Whitespace)
}
// END-TODO(MethodsAndMore)

class Tokenizer {
  const source: string
  var n: nat

  ghost predicate Valid()
    reads this
  {
    n <= |source|
  }

  constructor (s: string)
    ensures Valid() && source == s && n == 0
  {
    source, n := s, 0;
  }

  method Read() returns (cat: Category, ghost p: nat, token: string)
    requires Valid()
    modifies this
    // BEGIN-TODO(Read)
    ensures cat == End || cat == Error || Valid()
    ensures cat != Whitespace
    ensures old(n) <= p <= n <= |source|
    ensures cat == End <==> p == |source|
    ensures cat == End <==> p == n
    ensures forall i :: old(n) <= i < p ==> IsStart(source[i], Whitespace)
    ensures p < n ==> IsStart(source[p], cat)
    ensures forall i :: p + 1 <= i < n ==> IsFollow(source[i], cat)
    ensures p < n ==> n == |source| || !Is(source[n], cat)
    ensures token == source[p..n]
  {
    // skip whitespace
    while n != |source| && IsStart(source[n], Whitespace)
      invariant old(n) <= n <= |source|
      invariant forall i :: old(n) <= i < n ==> IsStart(source[i], Whitespace)
    {
      n := n + 1;
    }
    p := n;

    if n >= |source| {
      cat := End;
      token := "";
      return;
    }

    // Determine syntactic category
    var ch := source[n];
    if IsStart(ch, Identifier) {
      cat := Identifier;
    } else if IsStart(ch, Number) {
      cat := Number;
    } else if IsStart(ch, Operator) {
      cat := Operator;
    } else {
      cat := Error;
    }

    // read token
    var i := n;
    i := i + 1;

    while i < |source| && IsFollow(source[i], cat)
      invariant n <= i <= |source|
      invariant forall j :: n <= j < i ==> IsFollow(source[j], cat)
    {
      i := i + 1;
    }

    token := source[n..i];
    n := i;
  }
  // END-TODO(Read)
}
