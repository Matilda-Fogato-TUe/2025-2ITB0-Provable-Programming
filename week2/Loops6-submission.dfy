// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// You got this!!
//
// END-TODO(Name)



/* == Handout question 4.1.13 ==
 * Write a method that calculates the cubic root of a natural number using in
 * arithmetic only additions and multiplications by a constant. See the book,
 * section 11.4, for a program that does something similar for the square root.
 * The specification is
 *
 * method CubicRoot(N: nat) returns (r: nat)
 *     ensures r * r * r <= N < (r + 1) * (r + 1) * (r + 1)
 *
 * Make four, verifying, versions of increasing subtlety as follows. */

/* (a) The first version CubicRoot0 has only a specification of the loop, i.e.,
 * an invariant but not a body. It uses the invariant finding (loop design)
 * technique 11.0 of omitting a conjunct. */
method CubicRoot0(N: nat) returns (r: nat)
  // BEGIN-TODO(Version1)
  ensures r * r * r <= N < (r + 1) * (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) * (r + 1) <=N
    invariant r * r * r <= N
}
// END-TODO(Version1)

/* (b) The second version CubicRoot1 is a straightforward implementation of the
 * loop designed in the previous step. In this not so efficient program, every
 * cycle of the loop (r + 1) * (r + 1) * (r + 1) is calculated. */
method CubicRoot1(N: nat) returns (r: nat)
  // BEGIN-TODO(Version2)
  ensures r * r * r <= N < (r + 1) * (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) * (r + 1) <=N
    invariant r * r * r <= N
  {
    r := r + 1;
  }
}
// END-TODO(Version2)


/* (c) The third version CubicRoot2 exploits the invariant finding (loop design)
 * technique 11.1 of programming by wishing (also known as strengthening the
 * invariant) to avoid calculating the cubic. It still calculates a square every
 * cycle of the loop. */
method CubicRoot2(N: nat) returns (r: nat)
  // BEGIN-TODO(Version3)
  ensures r * r * r <= N < (r + 1) * (r + 1) * (r + 1)
{
  r := 0;
  var c := 1;
  while c <= N
    invariant r * r * r <= N
    invariant c == (r + 1) * (r + 1) * (r + 1)
  {
    c := c + (3 * r * r) + 9 * r + 7;
    r := r + 1;
  }
}
// END-TODO(Version3)


/* (d) The fourth and last version CubicRoot3 uses this technique again to avoid
 * calculating the square and only use multiplication by a constant, and
 * addition. */
method CubicRoot3(N: nat) returns (r: nat)
  // BEGIN-TODO(Version4)
  ensures r * r * r <= N < (r + 1) * (r + 1) * (r + 1)
{
  r := 0;
  var c := 1;
  var s := 1;
  while c <= N
    invariant r * r * r <= N
    invariant c == (r + 1) * (r + 1) * (r + 1)
    invariant s == (r + 1) * (r + 1)
  {
    s := s + 2 * r + 3;
    c := c + 3 * s - 3 * r - 5;
    r := r + 1;
  }
}
// END-TODO(Version4)