# Week 1 Assignment Questions

## Provable Programming Exercises  
*Kees Huizing, Wieger Wesselink*


### 1. (Handout 1.5bis)
Given is the formula:

- **(a)** Prove this formula by giving a derivation in the flag proof system of the course *Logic and Set Theory* (do not submit this).
- **(b)** Write this derivation in Dafny, following the same steps.  
  *Hint:* Use the Dafny construct `forall … ensures` as the parallel of `-introduction`.
- **(c)** The formula also verifies in Dafny without intermediate steps. Try this. *(Do not submit this.)*
- **(d)** Consider the signature given for this exercise’s lemma. Consider how this signature can be changed without changing its meaning, by modifying pre- and postconditions.

### 2. (Handout 1.6bis)
Given is the formula:

- **(a)** Prove this formula by giving a derivation in the flag proof system of the course *Logic and Set Theory* (do not submit this).
- **(b)** Write this derivation in Dafny, following the same steps.
- **(c)** The formula also verifies in Dafny without intermediate steps. Try this. *(Do not submit this.)*
- **(d)** Consider the signature given for this exercise’s lemma. Consider how this signature can be changed without changing its meaning, by modifying pre- and postconditions.

### 3. (Handout 1.3)
Consider a method that calculates whether all elements of sequence `a` are zero.

- **(a)** Specify this method. *Note that for an empty sequence, all elements are considered zero.*
- **(b)** Test this specification with at least four cases: two `true` and two `false`.  
  *Note:* Dafny needs a witness to prove that a `forall` formula does not hold.
- **(c)** Implement this method recursively and ensure that it verifies.  
  *Note:* Dafny does not allow method calls directly in expressions. To use the result of a method call in an expression, first assign the result to a variable.

### 4. (Handout 1.9)
The methods `Max` and `Negate` are not implemented. Nevertheless, we can write code that calls them and prove this code correct using their contracts.

- **(a)** Implement the method `Min` and ensure it verifies.

### 5. (Handout 1.10)
A word (or any sequence of elements) is a palindrome if it is equal to its reverse (e.g., `"racecar"` or `[1, 2, 3, 2, 1]`).

- **(a)** The method `IsPalindrome` checks whether a given string (`seq<char>`) is a palindrome.  
  The specification is provided. Implement it recursively and ensure that it verifies.

---


