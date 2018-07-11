
class Candidate {
    var winner: bool;
}

function Count(a: seq<Candidate>, s: int, t: int, x: Candidate): int
  requires 0 <= s <= t <= |a|
  ensures Count(a, s, t, x) == 0 || x in a
{
  if s == t then 0 else
  Count(a, s, t-1, x) + if a[t-1] == x then 1 else 0
}

function HasMajority(a: seq<Candidate>, s: int, t: int, x: Candidate) : bool
  requires 0 <= s <= t <= |a|
{
  2 * Count(a, s, t, x) > t - s
}

// Here is the first version of the algorithm, the one that assumes there is a majority choice.

method FindWinner(a: seq<Candidate>, K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{
  k := a[0];
  //var n, c, s := 1, 1, 0;
  var n := 1;
  var c := 1;
  var s := 0;
  while (n < |a|)
    invariant 0 <= s <= n <= |a|;
    invariant 2 * Count(a, s, |a|, K) > |a| - s;  // K has majority among a[s..]
    invariant 2 * Count(a, s, n, k) > n - s;  // k has majority among a[s..n]
    invariant c == Count(a, s, n, k);
    decreases  |a| - n;
  {
    if (a[n] == k) {
      n := n + 1;
      c := c + 1;
    } else if (2 * c > n + 1 - s) {
      n := n + 1;
    } else {
      n := n + 1;
      // We have 2*Count(a, s, n, k) == n-s, and thus the following lemma
      // lets us conclude 2*Count(a, s, n, K) <= n-s.
      Lemma_Unique(a, s, n, K, k);
      // We also have 2*Count(a, s, |a|, K) > |a|-s, and the following lemma
      // tells us Count(a, s, |a|, K) == Count(a, s, n, K) + Count(a, n, |a|, K),
      // and thus we can conclude 2*Count(a, n, |a|, K) > |a|-n.
      Lemma_Split(a, s, n, |a|, K);
      //k, n, c, s := a[n], n + 1, 1, n;
      k := a[n];
      n := n + 1;
      c := 1;
      s := n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);  // both k and K have a majority, so K == k
}


// Here are two lemmas about Count that are used in the methods above.

method Lemma_Split(a: seq<Candidate>, s: int, t: int, u: int, x: Candidate)
  requires 0 <= s <= t <= u <= |a|
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
{
  /* The postcondition of this method is proved automatically via Dafny's
     induction tactic.  But if a manual proof had to be provided, it would
     look like this:
  if (s != t) {
    Lemma_Split(a, s, t-1, u, x);
  }
  */
}

method Lemma_Unique(a: seq<Candidate>, s: int, t: int, x: Candidate, y: Candidate)
  requires 0 <= s <= t <= |a|
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
{
  /* The postcondition of this method is proved automatically via Dafny's
     induction tactic.  But if a manual proof had to be provided, it would
     look like this:
  if (s != t) {
    Lemma_Unique(a, s, t-1, x, y);
  }
  */
}
