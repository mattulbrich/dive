
class Node {
  var next: Node;

  function IsClosed(S: set<Node>) : bool
    //reads S
  {
    this in S && null in S &&
    forall n :: n in S && n != null && n.next != null ==> n.next in S
  }

  function Nexxxt(k: int, S: set<Node>): Node
    requires IsClosed(S) && 0 <= k
    ensures Nexxxt(k, S) in S  // a consequence of the definition
    //reads S
  {
    if k == 0 then this
    else if Nexxxt(k-1, S) == null then null
    else Nexxxt(k-1, S).next
  }

  function Reaches(sink: Node, S: set<Node>) : bool
    requires IsClosed(S)
    ensures Reaches(sink, S) ==> sink in S  // a consequence of the definition
    //reads S
  {
    exists k :: 0 <= k && Nexxxt(k, S) == sink
  }

  method Cyclic(ghost S: set<Node>) returns (reachesCycle: bool)
    requires IsClosed(S)
    ensures reachesCycle <==> exists n :: Reaches(n, S) && n.next != null && n.next.Reaches(n, S)
  {
    ghost var A, B := AnalyzeList(S);
    var tortoise, hare:= this, next;
    ghost var t, h := 0, 1;
    while hare != tortoise
      invariant tortoise != null && tortoise in S && hare in S
      invariant 0 <= t < h && Nexxxt(t, S) == tortoise && Nexxxt(h, S) == hare
      // What follows of the invariant is for proving termination:
      invariant h == 1 + 2*t && t <= A + B
      invariant forall k :: 0 <= k < t ==> Nexxxt(k, S) != Nexxxt(1+2*k, S)
      decreases A + B - t
    {
      if (hare == null || hare.next == null) {
        ghost var distanceToNull := if hare == null then h else h+1;
        Lemma_NullImpliesNoCycles(distanceToNull, S);
        assert !exists k,l :: 0 <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null && Nexxxt(k, S).next.Nexxxt(l, S) == Nexxxt(k, S);  // this is a copy of the postcondition of lemma NullImpliesNoCycles
        return false;
      }
      Lemma_NullIsTerminal(h+1, S);
      assert Nexxxt(t+1, S) != null;
      tortoise, t, hare, h := tortoise.next, t+1, hare.next.next, h+2;
      CrucialLemma(A, B, S);
    }
    Lemma_NullIsTerminal(h, S);
    Lemma_NexxxtIsTransitive(t+1, h - (t+1), S);
    assert tortoise.next.Reaches(tortoise, S);
    return true;
  }

  // What follows in this file are details that are relevant only to the proof.  That is,
  // to trust that the algorithm is correct, it is not necessary to go through the
  // details below--the specification of 'Cyclic' above and the fact that Dafny verifies
  // the program suffice.  (Of course, one also needs to trust the verifier.)

  lemma AnalyzeList(S: set<Node>) returns (A: int, B: int)
    requires IsClosed(S)
    // find an A and B (0 <= A && 1 <= B) such that:
    // the first A steps are no on a cycle, and
    // either next^A == null or next^A == next^(A+B).
    ensures 0 <= A && 1 <= B
    ensures Nexxxt(A, S) != null ==> Nexxxt(A, S) == Nexxxt(A, S).Nexxxt(B, S)
    ensures forall k,l :: 0 <= k < l < A ==> Nexxxt(k, S) != Nexxxt(l, S)
  {
    // since S is finite, we can just go ahead and compute the transitive closure of "next" from "this"
    var p, steps, Visited, NexxxtInverse: map<Node?,int> := this, 0, {null}, map[];
    while p !in Visited
      invariant 0 <= steps && p == Nexxxt(steps, S) && p in S && null in Visited && Visited <= S
      invariant forall t :: 0 <= t < steps ==>
         Nexxxt(t, S) in Visited &&
         Nexxxt(t, S) in NexxxtInverse && NexxxtInverse[Nexxxt(t, S)] == t
      invariant forall q :: q in Visited && q != null ==>
         q in NexxxtInverse && 0 <= NexxxtInverse[q] < steps && Nexxxt(NexxxtInverse[q], S) == q
      decreases S - Visited
    {
      p, steps, Visited, NexxxtInverse := p.next, steps + 1, Visited + {p}, NexxxtInverse[p := steps];
    }
    if p == null {
      A, B := steps, 1;
    } else {
      A := NexxxtInverse[p];
      B := steps - A;
      Lemma_NexxxtIsTransitive(A, B, S);
    }
  }

  lemma CrucialLemma(a: int, b: int, S: set<Node>)
    requires IsClosed(S)
    requires 0 <= a && 1 <= b
    requires forall k,l :: 0 <= k < l < a ==> Nexxxt(k, S) != Nexxxt(l, S)
    requires Nexxxt(a, S) == null || Nexxxt(a, S).Nexxxt(b, S) == Nexxxt(a, S)
    ensures exists T :: 0 <= T < a+b && Nexxxt(T, S) == Nexxxt(1+2*T, S)
  {
    if Nexxxt(a, S) == null {
      Lemma_NullIsTerminal(1+2*a, S);
      assert Nexxxt(a, S) == null ==> Nexxxt(1+2*a, S) == null;
    } else {
      assert Nexxxt(a, S) != null && Nexxxt(a, S).Nexxxt(b, S) == Nexxxt(a, S);
      Lemma_NexxxtIsTransitive(a, b, S);
      assert Nexxxt(a + b, S) == Nexxxt(a, S);
      // When the tortoise has done "a" steps, both it and the hare have reached the cycle.
      // Since the cycle has length "b", the hare has at most "b" steps to catch up with the
      // tortoise.  Well, you may think of the tortoise as being the one that has to catch up,
      // since the tortoise has not traveled as far.  So, let's imagine a virtual tortoise
      // that is in the same position as the tortoise, but who got there by taking at least
      // as many steps as the hare (but fewer than "b" steps more than the hare).
      var t, h := a, 1+2*a;  // steps traveled by the tortoise and the hare, respectively
      var vt := a;  // steps traveled by the virtual tortoise
      while vt < h
        invariant t <= vt < h+b
        invariant Nexxxt(t, S) == Nexxxt(vt, S)
      {
        Lemma_AboutCycles(a, b, vt, S);
        vt := vt + b;  // let the virtual tortoise take another lap
      }
      // Good.  Since the virtual tortoise has now taken at least as many steps as the hare,
      // we can compute (as a non-negative number) the steps that hare is trailing behind the
      // virtual tortoise.
      var catchup := vt - h;
      assert 0 <= catchup < b;
      // Now, let the hare catch up with the virtual tortoise by simulating "catchup" steps
      // of the algorithm.
      var i := 0;
      while i < catchup
        invariant 0 <= i <= catchup
        invariant t == a + i && h == 1 + 2*t && t <= vt
        invariant Nexxxt(t, S) == Nexxxt(vt, S) == Nexxxt(h + catchup - i, S)
      {
        i, t, vt, h := i+1, t+1, vt+1, h+2;
      }
      assert a <= t < a + b && Nexxxt(t, S) == Nexxxt(1 + 2*t, S);
    }
  }

  lemma Lemma_AboutCycles(a: int, b: int, k: int, S: set<Node>)
    requires IsClosed(S)
    requires 0 <= a <= k && 1 <= b && Nexxxt(a, S) != null && Nexxxt(a, S).Nexxxt(b, S) == Nexxxt(a, S)
    ensures Nexxxt(k + b, S) == Nexxxt(k, S)
  {
    Lemma_NexxxtIsTransitive(a, b, S);
    var n := a;
    while n < k
      invariant a <= n <= k
      invariant Nexxxt(n + b, S) == Nexxxt(n, S)
    {
      n := n + 1;
    }
  }

  lemma Lemma_NexxxtIsTransitive(x: int, y: int, S: set<Node>)
    requires IsClosed(S) && 0 <= x && 0 <= y
    ensures Nexxxt(x, S) != null ==> Nexxxt(x, S).Nexxxt(y, S) == Nexxxt(x + y, S)
  {
    if Nexxxt(x, S) != null
    {
      assert forall j :: 0 <= j ==> Nexxxt(x, S).Nexxxt(j, S) == Nexxxt(x + j, S);  // Dafny's induction tactic kicks in
      /* Alternatively, here's a manual proof by induction (but only up to the needed y):
      var j := 0;
      while j < y
        invariant 0 <= j <= y;
        invariant Nexxxt(x, S).Nexxxt(j, S) == Nexxxt(x + j, S);
      {
        j := j + 1;
      }
      */
    }
  }

  lemma Lemma_NullIsTerminal(d: int, S: set<Node>)
    requires IsClosed(S) && 0 <= d
    ensures forall k :: 0 <= k < d && Nexxxt(d, S) != null ==> Nexxxt(k, S) != null
  {
    var j := d;
    while 0 < j
      invariant 0 <= j <= d
      invariant forall k :: j <= k < d && Nexxxt(k, S) == null ==> Nexxxt(d, S) == null
    {
      j := j - 1;
      if Nexxxt(j, S) == null {
        assert Nexxxt(j+1, S) == null;
      }
    }
  }

  lemma Lemma_NullImpliesNoCycles(n: int, S: set<Node>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures !exists k,l :: 0 <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null && Nexxxt(k, S).next.Nexxxt(l, S) == Nexxxt(k, S)
  {
    // The proof of this lemma is more complicated than necessary, because Dafny does not know that
    // "if P(k,l) holds for one arbitrary (k,l), then it holds for all (k,l)".
    Lemma_NullImpliesNoCycles_part0(n, S);
    Lemma_NullImpliesNoCycles_part1(n, S);
    Lemma_NullImpliesNoCycles_part2(n, S);
  }

  lemma Lemma_NullImpliesNoCycles_part0(n: int, S: set<Node>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures forall k,l :: n <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
  {
    assert forall k :: n <= k ==> Nexxxt(k, S) == null;  // Dafny proves this thanks to its induction tactic
  }

  lemma Lemma_NullImpliesNoCycles_part1(n: int, S: set<Node>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures forall k,l :: 0 <= k && n <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
  {
    // Each of the following assertions makes use of Dafny's induction tactic
    assert forall k,l {:matchinglooprewrite false} :: 0 <= k && 0 <= l && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) == Nexxxt(k+1+l, S);
    assert forall kl :: n <= kl ==> Nexxxt(kl, S) == null;
  }

  lemma Lemma_NullImpliesNoCycles_part2(n: int, S: set<Node>)
    requires IsClosed(S) && 0 <= n && Nexxxt(n, S) == null
    ensures forall k,l :: 0 <= k < n && 0 <= l < n && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
  {
    var kn := 0;
    while kn < n
      invariant 0 <= kn <= n
      invariant forall k,l :: 0 <= k < kn && 0 <= l < n && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
    {
      var ln := 0;
      while ln < n
        invariant 0 <= ln <= n
        invariant forall k,l :: 0 <= k < kn && 0 <= l < n && Nexxxt(k, S) != null && Nexxxt(k, S).next != null ==> Nexxxt(k, S).next.Nexxxt(l, S) != Nexxxt(k, S)
        invariant forall l :: 0 <= l < ln && Nexxxt(kn, S) != null && Nexxxt(kn, S).next != null ==> Nexxxt(kn, S).next.Nexxxt(l, S) != Nexxxt(kn, S)
      {
        if Nexxxt(kn, S) != null && Nexxxt(kn, S).next != null {
          assert Nexxxt(kn+1, S) != null;
          Lemma_NexxxtIsTransitive(kn+1, ln, S);
          assert Nexxxt(kn, S).next.Nexxxt(ln, S) == Nexxxt(kn+1+ln, S);  // follows from the transitivity lemma on the previous line
          Lemma_NexxxtIsTransitive(kn, 1+ln, S);
          assert Nexxxt(kn+1+ln, S) == Nexxxt(kn, S).Nexxxt(1+ln, S);  // follows from the transitivity lemma on the previous line
          // finally, here comes the central part of the argument, namely:
          // if Nexxxt(kn, S).Nexxxt(1+ln, S) == Nexxxt(kn, S), then for any h (0 <= h), Nexxxt(kn, S).Nexxxt(h*(1+ln), S) == Nexxxt(kn, S), but
          // that can't be for n <= h*(1+ln), since Nexxxt(kn, S) != null and Nexxxt(n.., S) == null.
          if Nexxxt(kn, S).Nexxxt(1+ln, S) == Nexxxt(kn, S) {
            var nn := 1+ln;
            while nn < n
              invariant 0 <= nn
              invariant Nexxxt(kn, S).Nexxxt(nn, S) == Nexxxt(kn, S)
            {
              assert Nexxxt(kn, S) ==
                     Nexxxt(kn, S).Nexxxt(nn, S) ==
                     Nexxxt(kn, S).Nexxxt(1+ln, S) ==
                     Nexxxt(kn, S).Nexxxt(nn, S).Nexxxt(1+ln, S);
              Nexxxt(kn, S).Lemma_NexxxtIsTransitive(1+ln, nn, S);
              assert Nexxxt(kn, S).Nexxxt(nn+1+ln, S) == Nexxxt(kn, S);
              nn := nn + 1+ln;
            }
            Lemma_NexxxtIsTransitive(kn, nn, S);
            assert Nexxxt(kn, S).Nexxxt(nn, S) == Nexxxt(kn+nn, S);
            assert forall j :: n <= j ==> Nexxxt(j, S) == null;  // this uses Dafny's induction tactic
            assert false;  // we have reached a contradiction
          }
          assert Nexxxt(kn+1, S).Nexxxt(ln, S) != Nexxxt(kn, S);
        }
        ln := ln + 1;
      }
      kn := kn + 1;
    }
  }
}
