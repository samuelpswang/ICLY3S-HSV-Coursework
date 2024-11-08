// Filename: FullerWang.dfy
// Author: Josh Fuller, Samuel Wang
// Purpose: Hardware and Software Verification - Dafny Coursework 2024
// Last Updated: 02 Nov 2024

type symbol = int
type literal = (symbol,bool)
type clause = seq<literal>
type query = seq<clause>
type valuation = map<symbol,bool>

// extracts the set of symbols from a given clause
function symbols_clause(c:clause) : set<symbol>
ensures (forall xb :: xb in c ==> xb.0 in symbols_clause(c))
ensures (forall x :: (x in symbols_clause(c)) ==> (exists b :: (x,b) in c))
{
  if c == [] then {} else 
    assert forall xb :: xb in c ==> xb in {c[0]} || xb in c[1..];
    {c[0].0} + symbols_clause(c[1..])
}

// extracts the set of symbols from a given query
function symbols(q:query) : set<symbol>
{
  if q == [] then {} else
    symbols(q[1..]) + symbols_clause(q[0])
}

// evaluates the given clause under the given valuation
predicate evaluate_clause(c:clause, r:valuation) {
  exists xb :: (xb in c) && (xb in r.Items)
}

// evaluates the given query under the given valuation
predicate evaluate(q:query, r:valuation) {
  forall i :: 0 <= i < |q| ==> evaluate_clause(q[i], r)
}


///////////////////////////////////
// TASK 1: Duplicate-free sequences
///////////////////////////////////

// holds if a sequence of symbols has no duplicates
predicate dupe_free(xs:seq<symbol>) 
{
  forall i,j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}

// Part (a): reversing a dupe-free sequence (recursive implementation)
method rev(xs:seq<symbol>) returns (ys:seq<symbol>)
  requires dupe_free(xs)
  ensures dupe_free(ys)
  ensures |xs| == |ys|
  ensures forall i :: (0 <= i < |ys| ==> ys[i] == xs[|xs|-1-i])
{
  if (xs == [])
  {
    ys := [];
  }
  else 
  {
    ys := rev(xs[1..]);
    ys := ys + [xs[0]];
  }
}

// Part (b): reversing a dupe-free sequence (iterative implementation)
method rev2(xs:seq<symbol>) returns (ys:seq<symbol>)
  requires dupe_free(xs)
  ensures dupe_free(ys)
  ensures |xs| == |ys|
  ensures forall i :: (0 <= i < |ys| ==> ys[i] == xs[|xs|-1-i])
{
  if (xs == [])
  {
    ys := [];
  }
  else
  {
    ys := [];
    var i := 0;
    while (i < |xs|)
      invariant dupe_free(xs)
      invariant i <= |xs|
      invariant dupe_free(ys)
      invariant i == |ys|
      invariant forall j :: (0 <= j < |ys| ==> ys[j] == xs[i-1-j])
    {
      ys := [xs[i]] + ys;
      i := i + 1;
    }
  }
}

// Part (c): concatenating two dupe-free sequences
lemma dupe_free_concat(xs:seq<symbol>, ys:seq<symbol>)
  requires dupe_free(xs)
  requires dupe_free(ys)
  requires forall i,j :: 0 <= i < |xs| && 0 <= j < |ys| ==> xs[i] != ys[j]
  ensures dupe_free (xs + ys)
{
}
// Conditions where only dupe_free(xs) and dupe_free(ys) is not sufficient:
// xs: [1, 2, 3], ys: [1, 2, 3]
// --> xs+ys: [1, 2, 3, 1, 2, 3] --> dupe_free(xs+ys) is false


//////////////////////////////////////////
// TASK 2: Extracting symbols from queries
//////////////////////////////////////////

// remove the given set of symbols from a clause
function remove_symbols_clause(c:clause, xs:set<symbol>) : clause
  ensures symbols_clause(remove_symbols_clause(c, xs)) == symbols_clause(c) - xs
  ensures (forall x :: x in xs && x !in symbols_clause(c)) ==> (remove_symbols_clause(c, xs) == c)
{
  if c == [] then [] else
    var c' := remove_symbols_clause(c[1..], xs);
    if c[0].0 in xs then c' else [c[0]] + c'
}

// remove the given set of symbols from a query
function remove_symbols(q:query, xs:set<symbol>) : query
  ensures symbols(remove_symbols(q, xs)) == symbols(q) - xs
{
  if q == [] then [] else
    [remove_symbols_clause(q[0], xs)] + remove_symbols(q[1..], xs)
}

// Part (a): extract the sequence of symbols that appear in a clause
function symbol_seq_clause(c:clause) : seq<symbol>
  ensures dupe_free(symbol_seq_clause(c))
  ensures forall x :: x in symbol_seq_clause(c) <==> x in symbols_clause(c)
  decreases |symbols_clause(c)|
{
  if c == [] then [] else
    var x := c[0].0;
    var c' := remove_symbols_clause(c[1..], {x});
    [x] + symbol_seq_clause(c')
}

// Part (b): extract the sequence of symbols that appear in a query
lemma remove_symbols_func_may_decrease_size(q:query, xs:set<symbol>)
  ensures |remove_symbols(q, xs)| <= |q|
{
}

lemma mutually_exclusive_is_dupe_free_concat_able(seq1: seq<symbol>, seq2:seq<symbol>)
  requires forall x :: x in seq1 ==> !(x in seq2)
  requires forall x :: x in seq2 ==> !(x in seq1)
  requires dupe_free(seq1)
  requires dupe_free(seq2)
  ensures dupe_free(seq1 + seq2)
{
  assert forall i :: 0 <= i < |seq1| ==> !(seq1[i] in seq2);
  assert forall i :: 0 <= i < |seq2| ==> !(seq2[i] in seq1);
  assert forall i,j :: 0 <= i < |seq1| && 0 <= j < |seq2| ==> seq1[i] != seq2[j]; 
  dupe_free_concat(seq1, seq2);
}

function symbol_seq(q:query) : seq<symbol>
  ensures dupe_free(symbol_seq(q))
  ensures forall x :: x in symbol_seq(q) <==> x in symbols(q)
  decreases |q|
{
  if q == [] then [] else
    var xs := symbols_clause(q[0]);
    var q' := remove_symbols(q[1..], xs);
    remove_symbols_func_may_decrease_size(q[1..], xs);
    mutually_exclusive_is_dupe_free_concat_able(symbol_seq_clause(q[0]), symbol_seq(q'));
    symbol_seq_clause(q[0]) + symbol_seq(q')
}


/////////////////////////////
// TASK 3: Evaluating queries
/////////////////////////////

// evaluate the given clause under the given valuation (imperative version)
method eval_clause (c:clause, r:valuation) returns (result: bool)
  ensures result == evaluate_clause(c,r)
{
  var i := 0;
  while (i < |c|)
    invariant i <= |c|
    invariant forall j :: 0 <= j < i ==> !(c[j] in r.Items)
  {
    if (c[i] in r.Items)
    {
      return true;
    }
    i := i + 1;
  }
  return false;
}

// evaluate the given query under the given valuation (imperative version)
method eval(q:query, r:valuation) returns (result: bool)
  ensures result == evaluate(q,r)
{
  var i := 0;
  while (i < |q|)
    invariant i <= |q|
    invariant forall j :: 0 <= j < i ==> evaluate_clause(q[j],r)
  {
    result := eval_clause(q[i], r);
    if (!result) {
      return false;
    }
    i := i + 1;
  }
  return true;
}


/////////////////////////////////////////////
// TASK 4: Verifying a brute-force SAT solver
/////////////////////////////////////////////

// prepends (x,b) to each valuation in a given sequence 
function map_prepend (x:symbol, b:bool, rs:seq<valuation>) : seq<valuation>
{
  if rs == [] then [] else
    [rs[0][x:=b]] + map_prepend(x,b,rs[1..])
}

// constructs all possible valuations of the given symbols
function mk_valuation_seq (xs: seq<symbol>) : seq<valuation>
{
  if xs == [] then [ map[] ] else
    var rs := mk_valuation_seq(xs[1..]);
    var x := xs[0];
    map_prepend(x,true,rs) + map_prepend(x,false,rs)
}

// A brute-force SAT solver. Given a query, it constructs all possible 
// valuations over the symbols that appear in the query, and then 
// iterates through those valuations until it finds one that works.
method naive_solve (q:query) returns (sat:bool, r:valuation)
  ensures sat==true ==> evaluate(q,r)
  ensures sat==false ==> forall r:valuation :: r in mk_valuation_seq(symbol_seq(q)) ==> !evaluate(q,r)
{
  var xs := symbol_seq(q);
  var rs := mk_valuation_seq(xs);
  sat := false;
  var i := 0;
  while (i < |rs|)
    invariant i <= |rs|
    invariant forall j :: 0 <= j < i ==> !evaluate(q,rs[j])
  {
    sat := eval(q, rs[i]);
    if (sat) {
      return true, rs[i];
    }
    i := i + 1;
  }
  return false, map[];
}


////////////////////////////////////////
// TASK 5: Verifying a simple SAT solver
////////////////////////////////////////

// This function updates a clause under the valuation x:=b. 
// This means that the literal (x,b) is true. So, if the clause
// contains the literal (x,b), the whole clause is true and can 
// be deleted. Otherwise, all occurrences of (x,!b) can be 
// removed from the clause because those literals are false and 
// cannot contribute to making the clause true.
function update_clause (x:symbol, b:bool, c:clause) : query
{
  if ((x,b) in c) then [] else [remove_symbols_clause(c,{x})]
}

// This function updates a query under the valuation x:=b. It
// invokes update_clause on each clause in turn.
function update_query (x:symbol, b:bool, q:query) : query
{
  if q == [] then [] else
    var q_new := update_clause(x,b,q[0]);
    var q' := update_query(x,b,q[1..]);
    q_new + q'
}

// Updating a query under the valuation x:=b is the same as updating 
// the valuation itself and leaving the query unchanged.
lemma evaluate_is_and(q1:query, q2:query, r:valuation)
  ensures evaluate(q1+q2, r) == (evaluate(q1,r) && evaluate(q2,r))
{
  var q' := q1 + q2;
  assert evaluate(q',r) == (forall i :: 0 <= i < |q'| ==> evaluate_clause(q'[i],r));

  assert q1 == q'[0..|q1|];
  assert evaluate(q1,r) == evaluate(q'[0..|q1|], r);

  assert q2 == q'[|q1|..];
  assert evaluate(q2,r) == evaluate(q'[|q1|..], r);

  assert (forall i :: 0 <= i < |q'| ==> evaluate_clause(q'[i],r)) == 
    ((forall i :: 0 <= i < |q1| ==> evaluate_clause(q'[i],r)) && 
    (forall i :: |q1| <= i < |q'| ==> evaluate_clause(q'[i],r)));
}

lemma evaluate_query_is_evaluate_clause(x:symbol, b:bool, r:valuation, q:query)
  ensures evaluate(q, r) == (forall c :: c in q ==> evaluate_clause(c, r))
{}

lemma evalute_update_query_is_evaluate_udpate_clause(x:symbol, b:bool, r:valuation, q:query)
  ensures evaluate(update_query(x, b, q), r) == (forall c :: c in q ==> evaluate(update_clause(x, b, c), r))
{
  var q' := update_query(x, b, q);
  assert evaluate(q', r) == (forall c' :: c' in q' ==> evaluate_clause(c', r));
}

lemma update_clause_does_not_incl_x(x:symbol, b:bool, c:clause)
  ensures forall i :: 0 <= i < |update_clause(x,b,c)| ==> (x,b) !in update_clause(x,b,c)[i]
  ensures forall i :: 0 <= i < |update_clause(x,b,c)| ==> (x,!b) !in update_clause(x,b,c)[i]
{
}

lemma untitled4(c:clause, r:valuation)
  ensures evaluate_clause(c,r) <==> (exists i :: 0 <= i < |c| && c[i] in r.Items)
{
}

lemma untitled2(x:symbol, b:bool, c:clause, r:valuation)
  requires x !in r.Keys
  // requires (x,b) !in c
  // requires (x,!b) !in c
  ensures evaluate_clause(c,r) == evaluate_clause(c+[(x,b)],r)
{

}

lemma untitled3(x:symbol, b:bool, c:clause, r:valuation)
  requires x !in r.Keys
  requires (x,b) !in c
  requires (x,!b) !in c
  ensures evaluate_clause(c,r) == evaluate_clause(c,r[x:=b])
{
  assert (x,b) !in c ==> forall i :: (0 <= i < |c| ==> c[i] != (x,b));
}

lemma untitled6(c: clause, xs: set<symbol>)
  ensures forall xb :: xb in remove_symbols_clause(c,xs) ==> xb in c
{}

lemma untitled5(x:symbol,b:bool,c:clause)
  requires (x,b) !in c 
  ensures forall xb :: xb in update_clause(x,b,c)[0] ==> xb in c
{
  var c' := update_clause(x,b,c)[0];
  assert c' == remove_symbols_clause(c, {x});
  untitled6(c,{x});
  assert forall xb :: xb in remove_symbols_clause(c, {x}) ==> xb in c;
}

lemma untitled8(c:clause, xs:set<symbol>)
  ensures forall xb :: xb in c && xb.0 !in xs ==> xb in remove_symbols_clause(c,xs)
{
}

lemma untitled9(x:symbol, xs:set<symbol>)
  requires |xs| == 1 && x in xs
  ensures xs == {x}
{
  if (xs > {x})
  {
    assert |xs - {x}| >= 1 ==> |xs| > 1;
    assert |xs| == 1 && |xs| > 1;
    assert false;
  }
}

lemma untitled10(x:symbol, xs:set<symbol>, y:symbol)
  requires |xs| == 1 && x in xs
  ensures y !in xs ==> y != x
{
}

lemma untitled11(c:clause, xs:set<symbol>, x:symbol)
  requires |xs| == 1 && x in xs
  ensures forall xb :: xb in c && xb.0 !in xs ==> xb in c && xb.0 != x
{
}

lemma untitled13(x:symbol, xs:set<symbol>, y:symbol)
  requires |xs| == 1 && x in xs
  ensures y in xs ==> y == x
{
  untitled9(x, xs);
}

lemma untitled12(c:clause, xs:set<symbol>, x:symbol)
  requires |xs| == 1 && x in xs
  ensures forall xb :: xb in c && xb.0 in xs ==> xb in c && xb.0 == x
{
  assert forall xb :: xb in c ==> (xb.0 in xs) || (xb.0 !in xs);
  untitled11(c, xs, x);
  assert forall xb :: xb in c && xb.0 in xs ==> xb in c;

  untitled9(x, xs);
  assert xs == {x};
  assert forall xb :: xb in c && xb.0 in xs ==> xb.0 == x;
}

lemma untitled7(c: clause, xs: set<symbol>, b:bool, x:symbol)
  requires |xs| == 1
  requires x in xs
  requires (x,b) in c
  requires (x,!b) !in c
  ensures forall xb :: (xb in c) ==> (xb in remove_symbols_clause(c,xs)+[(x,b)])
{
  var c' := remove_symbols_clause(c,xs);
  untitled6(c,xs);
  assert forall xb :: xb in c' ==> xb in c;
  assert forall xb :: xb in [(x,b)] ==> xb in c;
  assert forall xb :: xb in c'+[(x,b)] ==> xb in c;

  untitled8(c,xs);
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c';
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c'+[(x,b)];

  untitled11(c, xs, x);
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c && (xb.0 != x) ==> xb in c'+[(x,b)];
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c'+[(x,b)];

  untitled12(c, xs, x);
  assert forall xb :: xb in c ==> (xb.1 == true || xb.1 == false);
  assert forall xb :: xb in c && (xb.0 in xs) ==> xb in c && (xb.0 == x) ==> xb == (x,b) ==> xb in c'+[(x,b)];
  assert forall xb :: xb in c && (xb.0 in xs) ==> (xb in c && (xb.0 == x) ==> xb in c'+[(x,b)]);
  assert forall xb :: xb in c && (xb.0 in xs) ==> (xb in c'+[(x,b)]);

  assert forall xb :: xb in c ==> xb in c'+[(x,b)];
}

lemma untitled(x:symbol, b:bool, c:clause, r:valuation)
  requires x !in r.Keys
  requires (x,b) !in c && (x,!b) in c
  ensures evaluate_clause(update_clause(x,b,c)[0], r) == evaluate_clause(c, r[x:=b])
  ensures (x !in r.Keys) && (x,b) !in c && (x,!b) in c ==> evaluate_clause(update_clause(x,b,c)[0], r) == evaluate_clause(c, r[x:=b])
  ensures evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r)
  // ensures forall c':clause :: (x !in r.Keys) && (x,b) !in c' && (x,!b) in c' ==> evaluate_clause(update_clause(x,b,c')[0], r) == evaluate_clause(c', r[x:=b])
{
  var c' := update_clause(x,b,c)[0];
  untitled5(x,b,c);
  assert forall xb :: xb in c' ==> xb in c;
  var r' := r[x:=b];

  assert (x,b) !in c';
  assert (x,!b) !in c';
  assert x !in r.Keys;
  assert x in r'.Keys;

  // assert evaluate_clause(c,r') == evaluate_clause(c',r');

  untitled3(x,b,c',r);
  assert evaluate_clause(c',r) == evaluate_clause(c',r[x:=b]);
  assert evaluate_clause(c',r) == evaluate_clause(c', r');

  untitled2(x,!b,c',r);
  assert evaluate_clause(c',r) == evaluate_clause(c'+[(x,!b)], r);

  untitled7(c, {x}, !b, x);
  assert forall xb :: xb in c'+[(x,!b)] ==> xb in c;
  assert forall xb :: xb in c ==> xb in c'+[(x,!b)];
  assert evaluate_clause(c',r) == evaluate_clause(c,r);

  // assert evaluate_clause(c', r) ==> exists xb :: (xb in c') && (xb in r.Items);
  // assert evaluate_clause(c', r) ==> exists xb :: (xb in c'+[(x,b)]) && (xb in r.Items);
  // assert evaluate_clause(c', r) ==> exists xb :: (xb in c'+[(x,!b)]) && (xb in r.Items);
  // assert evaluate_clause(c', r) ==> exists xb :: (xb in c'+[(x,!b)]) && (xb in r[x:=b].Items);
  // assert evaluate_clause(c', r) ==> exists xb :: (xb in c'+[(x,!b)]) && (xb in r'.Items);
  // // assert evaluate_clause(c', r) ==> exists xb :: (xb in c) && (xb in r'.Items);
  // assert evaluate_clause(c', r) ==> evaluate_clause(c, r');
  // // assert evaluate_clause(c', r) ==> evaluate_clause(c'+[(x,!b)], r') ==> evaluate_clause(c, r');

  // assert evaluate_clause(c, r') ==> exists xb :: (xb in c) && (xb in r'.Items);
  // assert (x,!b) !in r'.Items;
  // assert evaluate_clause(c, r') ==> exists xb :: (xb in c'+[(x,!b)]) && (xb in r'.Items);
  // // assert evaluate_clause(c, r') ==> evaluate_clause(c', r);

  // assert evaluate_clause(c', r) <==> evaluate_clause(c, r');
  assert evaluate_clause(c', r) == evaluate_clause(c, r');

  // assert forall cx:clause :: (x,b) !in cx && (x,!b) in cx ==> evaluate_clause(update_clause(x,b,cx)[0], r) == evaluate_clause(cx, r[x:=b]);
  // assert forall cx:clause :: (x !in r.Keys) && (x,b) !in cx && (x,!b) in cx ==> evaluate_clause(update_clause(x,b,cx)[0], r) == evaluate_clause(cx, r[x:=b]);
}

lemma u1(c:clause, xs:set<symbol>)
  requires forall x :: x in xs ==> x !in symbols_clause(c)
  ensures remove_symbols_clause(c, xs) == c
{}

lemma u0(x:symbol, b:bool, r:valuation, c:clause)
  requires x !in r.Keys
  requires (x,b) !in c
  requires (x,!b) !in c
  ensures evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r)
{
  assert (x,b) !in c && (x,!b) !in c ==> x !in symbols_clause(c);
  var xs := {x};
  u1(c, xs);
  assert update_clause(x, b, c)[0] == c;
}

lemma evaluate_update_query(x:symbol, b:bool, r:valuation, q:query)
  requires x !in r.Keys
  ensures evaluate(update_query(x,b,q), r) == evaluate(q, r[x:=b])
{
  evaluate_query_is_evaluate_clause(x, b, r[x := b], q);
  evalute_update_query_is_evaluate_udpate_clause(x, b, r, q);
  forall c | c in q
    ensures evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r)
  {
    if (x,b) in c
    {
      assert evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
    }
    else 
    {
      if (x,!b) in c
      {
        untitled(x, b, c, r);
        assert evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
      }
      else
      {
        u0(x, b, r, c);
        assert evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
      }
      assert evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
    }
  }
  assert forall c :: c in q ==> evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
  assert (forall c :: c in q ==> evaluate_clause(c, r[x:=b])) == (forall c :: c in q ==> evaluate(update_clause(x, b, c), r));
}

// A simple SAT solver. Given a query, it does a three-way case split. If
// the query has no clauses then it is trivially satisfiable (with the
// empty valuation). If the first clause in the query is empty, then the
// query is unsatisfiable. Otherwise, it considers the first symbol that 
// appears in the query, and makes two recursive solving attempts: one 
// with that symbol evaluated to true, and one with it evaluated to false.
// If neither recursive attempt succeeds, the query is unsatisfiable.
method simp_solve (q:query) returns (sat:bool, r:valuation)
  ensures sat==true ==> evaluate(q,r)
  ensures sat==false ==> forall r :: !evaluate(q,r)
{
  if (q == []) {
    return true, map[];
  } else if (q[0] == []) {
    return false, map[];
  } else {
    var x := q[0][0].0;
    sat, r := simp_solve(update_query(x,true,q));
    if (sat) {
      r := r[x:=true];
      return;
    } 
    sat, r := simp_solve(update_query(x,false,q));
    if (sat) {
      r := r[x:=false];
      return;
    }
    return sat, map[];
  }
}

method Main ()
{
  var sat : bool;
  var r : valuation;
  var q1 := /* (a ∨ b) ∧ (¬b ∨ c) */ 
            [[(1, true), (2, true)], [(2, false), (3, true)]];
  var q2 := /* (a ∨ b) ∧ (¬a ∨ ¬b) */
            [[(1, true), (2, true)], [(1, false)], [(2, false)]];
  var q3 := /* (a ∨ ¬b) */
            [[(1, true), (2, false)]];
  var q4 := /* (¬b ∨ a) */
            [[(2, false), (1, true)]];
  
  var symbol_seq := symbol_seq(q1);
  print "symbols = ", symbol_seq, "\n";

  var rs := mk_valuation_seq(symbol_seq);
  print "all valuations = ", rs, "\n";
  
  sat, r := naive_solve(q1);
  print "solver = naive, q1 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q2);
  print "solver = naive, q2 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q3);
  print "solver = naive, q3 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q4);
  print "solver = naive, q4 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q1);
  print "solver = simp, q1 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q2);
  print "solver = simp, q2 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q3);
  print "solver = simp, q3 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q4);
  print "solver = simp, q4 result = ", sat, ", valuation = ", r, "\n";
}
