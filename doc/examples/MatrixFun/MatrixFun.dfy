method MirrorImage(m: array2<int>)
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==>
            m[i,j] == old(m[i, m.Length1-1-j])
  modifies {m}
{
  var a := 0;
  while a < m.Length0
    invariant a <= m.Length0
    invariant forall i,j :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==>
                m[i,j] == old(m[i, m.Length1-1-j])
    invariant forall i,j :: a <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
                m[i,j] == old(m[i,j])
  {
    var b := 0;
    while b < m.Length1 / 2
      invariant  b <= m.Length1 / 2
      invariant forall i,j :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==>
                  m[i,j] == old(m[i, m.Length1-1-j])
      invariant forall j :: 0 <= j && j < b ==>
                  m[a,j] == old(m[a, m.Length1-1-j]) &&
                  old(m[a,j]) == m[a, m.Length1-1-j]
      invariant forall j :: b <= j && j < m.Length1-b ==> m[a,j] == old(m[a,j])
      invariant forall i,j :: a+1 <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
                  m[i,j] == old(m[i,j])
    {
      m[a, m.Length1-1-b] := m[a, b];
      m[a, b] := m[a, m.Length1-1-b];
      b := b + 1;
    }
    a := a + 1;
  }
}

method Flip(m: array2<int>)
  requires m.Length0 == m.Length1
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i,j] == old(m[j,i])
  modifies {m}
{
  var N := m.Length0;
  var a := 0;
  var b := 1;
  while a != N
    invariant a < b <= N || (a == N && b == N+1)
    invariant forall i,j :: 0 <= i <= j < N ==>
                if i < a || (i == a && j < b)
                  then m[i,j] == old(m[j,i]) && m[j,i] == old(m[i,j])
                  else m[i,j] == old(m[i,j]) && m[j,i] == old(m[j,i])
    decreases {N-a, N-b};

  {
    if b < N {
      m[a,b] := m[b,a];
      m[b,a] := m[a,b];
      b := b + 1;
    } else {
      a := a + 1;
      b := a + 1;
    }
  }
}
