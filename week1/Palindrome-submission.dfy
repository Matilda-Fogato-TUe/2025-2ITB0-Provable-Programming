// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
// END-TODO(Name)



/* == Handout question 1.10 ==
 * A word, or in general any sequence of elements is a palindrome if the
 * sequence is equal to its reverse, e.g., "racecar" or [1, 2, 3, 2, 1]. The
 * method 'IsPalindrome` checks whether a given string (a sequence of
 * characters, a seq<char>) is a palindrome. The specification is given.
 * Implement it recursively and see that it verifies. */
method IsPalindrome(a: string) returns (p: bool)
  ensures p <==> forall i | 0 <= i < |a| / 2 :: a[i] == a[|a| - 1 - i]
// BEGIN-TODO(Implementation)
// Add your implementation here.
// END-TODO(Implementation)
