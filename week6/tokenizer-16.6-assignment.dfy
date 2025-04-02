// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// Add your modified implementation of the function Read
// END-TODO(Read)
}
