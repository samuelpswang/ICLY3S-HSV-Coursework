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
  ensures forall x :: x in symbols(q) <==> (exists i :: 0 <= i < |q| && x in symbols_clause(q[i]))
  ensures forall x :: x in symbols(q) <==> (exists c :: c in q && x in symbols_clause(c))
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
  if (xs == []) {
    ys := [];
  } else {
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
  decreases |c|
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
{}

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
  ensures (x in symbols_clause(c)) ==> symbols(update_clause(x, b, c)) < symbols_clause(c)
  ensures (x !in symbols_clause(c)) ==> symbols(update_clause(x, b, c)) == symbols_clause(c)
{
  if ((x,b) in c) then [] else [remove_symbols_clause(c,{x})]
}

// This function updates a query under the valuation x:=b. It
// invokes update_clause on each clause in turn.
function update_query(x:symbol, b:bool, q:query) : query
  ensures x !in symbols(update_query(x, b, q))
  ensures symbols(update_query(x, b, q)) <= symbols(q)
{
  if q == [] then [] else
    var q_new := update_clause(x,b,q[0]);
    var q' := update_query(x,b,q[1..]);
    excl_sym_in_q_is_additive(q_new, q', x);

    assert symbols(q_new) <= symbols(q);
    assert symbols(q') <= symbols(q[1..]);
    assert symbols(q_new) + symbols(q') <= symbols(q);
    assert symbols(q_new+q') == symbols(q_new) + symbols(q') <= symbols(q);

    q_new + q'
}

// BEGIN: Helper lemmas for evaluate_update_query and simp_solve
lemma excl_sym_in_c_eq_excl_sym_in_q(x:symbol, q:query)
  requires forall c :: c in q ==> x !in symbols_clause(c)
  ensures x !in symbols(q)
{}

lemma excl_sym_in_q_eq_excl_sym_in_c(x:symbol, q:query)
  requires x !in symbols(q)
  ensures forall c :: c in q ==> x !in symbols_clause(c)
{}

lemma excl_sym_in_q_is_additive(q1:query, q2:query, x:symbol)
  requires x !in symbols(q1)
  requires x !in symbols(q2)
  ensures x !in symbols(q1+q2)
{
  excl_sym_in_q_eq_excl_sym_in_c(x, q1);
  excl_sym_in_q_eq_excl_sym_in_c(x, q2);
  assert forall c :: c in q1+q2 ==> x !in symbols_clause(c);
  excl_sym_in_c_eq_excl_sym_in_q(x, q1+q2);
}

lemma  subset_query_concat_symbols(q1:query, q2:query)
  ensures symbols(q1) + symbols(q2) <= symbols(q1+q2)
{}

lemma evaluate_is_conjunctive_by_and(q1:query, q2:query, r:valuation)
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

lemma evaluate_clause_c_expansion(x:symbol, b:bool, c:clause, r:valuation)
  requires x !in r.Keys
  ensures evaluate_clause(c,r) == evaluate_clause(c+[(x,b)],r)
{}

lemma evaluate_clause_r_expansion(x:symbol, b:bool, c:clause, r:valuation)
  requires x !in r.Keys
  requires (x,b) !in c
  requires (x,!b) !in c
  ensures evaluate_clause(c,r) == evaluate_clause(c,r[x:=b])
{
  assert (x,b) !in c ==> forall i :: (0 <= i < |c| ==> c[i] != (x,b));
}

lemma if_present_in_removed_then_present_in_original(c: clause, xs: set<symbol>)
  ensures forall xb :: xb in remove_symbols_clause(c,xs) ==> xb in c
{}

lemma if_present_in_update_then_present_in_original(x:symbol,b:bool,c:clause)
  requires (x,b) !in c 
  ensures forall xb :: xb in update_clause(x,b,c)[0] ==> xb in c
{
  var c' := update_clause(x,b,c)[0];
  assert c' == remove_symbols_clause(c, {x});
  if_present_in_removed_then_present_in_original(c,{x});
  assert forall xb :: xb in remove_symbols_clause(c, {x}) ==> xb in c;
}

lemma if_xb_is_not_in_xs_then_in_removed(c:clause, xs:set<symbol>)
  ensures forall xb :: xb in c && xb.0 !in xs ==> xb in remove_symbols_clause(c,xs)
{}

lemma set_size_one_identity(x:symbol, xs:set<symbol>)
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

lemma set_size_one_clause_relation(c:clause, xs:set<symbol>, x:symbol)
  requires |xs| == 1 && x in xs
  ensures forall xb :: xb in c && xb.0 !in xs ==> xb in c && xb.0 != x
{}

lemma set_size_one_clause_relation2(c:clause, xs:set<symbol>, x:symbol)
  requires |xs| == 1 && x in xs
  ensures forall xb :: xb in c && xb.0 in xs ==> xb in c && xb.0 == x
{
  assert forall xb :: xb in c ==> (xb.0 in xs) || (xb.0 !in xs);
  set_size_one_clause_relation(c, xs, x);
  assert forall xb :: xb in c && xb.0 in xs ==> xb in c;

  set_size_one_identity(x, xs);
  assert xs == {x};
  assert forall xb :: xb in c && xb.0 in xs ==> xb.0 == x;
}

lemma if_xb_in_c_and_xnb_nin_c(c: clause, xs: set<symbol>, b:bool, x:symbol)
  requires |xs| == 1
  requires x in xs
  requires (x,b) in c
  requires (x,!b) !in c
  ensures forall xb :: (xb in c) ==> (xb in remove_symbols_clause(c,xs)+[(x,b)])
{
  var c' := remove_symbols_clause(c,xs);
  if_present_in_removed_then_present_in_original(c,xs);
  assert forall xb :: xb in c' ==> xb in c;
  assert forall xb :: xb in [(x,b)] ==> xb in c;
  assert forall xb :: xb in c'+[(x,b)] ==> xb in c;

  if_xb_is_not_in_xs_then_in_removed(c,xs);
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c';
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c'+[(x,b)];

  set_size_one_clause_relation(c, xs, x);
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c && (xb.0 != x) ==> xb in c'+[(x,b)];
  assert forall xb :: xb in c && (xb.0 !in xs) ==> xb in c'+[(x,b)];

  set_size_one_clause_relation2(c, xs, x);
  assert forall xb :: xb in c ==> (xb.1 == true || xb.1 == false);
  assert forall xb :: xb in c && (xb.0 in xs) ==> xb in c && (xb.0 == x) ==> xb == (x,b) ==> xb in c'+[(x,b)];
  assert forall xb :: xb in c && (xb.0 in xs) ==> (xb in c && (xb.0 == x) ==> xb in c'+[(x,b)]);
  assert forall xb :: xb in c && (xb.0 in xs) ==> (xb in c'+[(x,b)]);

  assert forall xb :: xb in c ==> xb in c'+[(x,b)];
}

lemma if_xb_in_c_and_xnb_in_c(x:symbol, b:bool, c:clause, r:valuation)
  requires x !in r.Keys
  requires (x,b) !in c && (x,!b) in c
  ensures evaluate_clause(update_clause(x,b,c)[0], r) == evaluate_clause(c, r[x:=b])
  ensures (x !in r.Keys) && (x,b) !in c && (x,!b) in c ==> evaluate_clause(update_clause(x,b,c)[0], r) == evaluate_clause(c, r[x:=b])
  ensures evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r)
{
  var c' := update_clause(x,b,c)[0];
  if_present_in_update_then_present_in_original(x,b,c);
  assert forall xb :: xb in c' ==> xb in c;
  var r' := r[x:=b];

  assert (x,b) !in c';
  assert (x,!b) !in c';
  assert x !in r.Keys;
  assert x in r'.Keys;

  evaluate_clause_r_expansion(x,b,c',r);
  assert evaluate_clause(c',r) == evaluate_clause(c',r[x:=b]);
  assert evaluate_clause(c',r) == evaluate_clause(c', r');

  evaluate_clause_c_expansion(x,!b,c',r);
  assert evaluate_clause(c',r) == evaluate_clause(c'+[(x,!b)], r);

  if_xb_in_c_and_xnb_nin_c(c, {x}, !b, x);
  assert forall xb :: xb in c'+[(x,!b)] ==> xb in c;
  assert forall xb :: xb in c ==> xb in c'+[(x,!b)];
  assert evaluate_clause(c',r) == evaluate_clause(c,r);

  assert evaluate_clause(c', r) == evaluate_clause(c, r');
}

lemma remove_sym_pass_through_if_x_not_present(c:clause, xs:set<symbol>)
  requires forall x :: x in xs ==> x !in symbols_clause(c)
  ensures remove_symbols_clause(c, xs) == c
{}

lemma if_xb_nin_c_and_xnb_nin_c(x:symbol, b:bool, r:valuation, c:clause)
  requires x !in r.Keys
  requires (x,b) !in c
  requires (x,!b) !in c
  ensures evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r)
{
  assert (x,b) !in c && (x,!b) !in c ==> x !in symbols_clause(c);
  var xs := {x};
  remove_sym_pass_through_if_x_not_present(c, xs);
  assert update_clause(x, b, c)[0] == c;
}

lemma x_in_r_keys(x:symbol,r:valuation)
  requires x in r.Keys
  ensures ((x,true) in r.Items || (x, false) in r.Items)
{
  assert x in r.Keys;
  assert r[x] == true || r[x] == false;
  assert r[x] == true ==> (x,true) in r.Items;
  assert exists b :: (x,b) in r.Items;
}

lemma x_in_r_keys_general(r:valuation)
  ensures forall x:symbol :: (x in r.Keys) ==> ((x,true) in r.Items || (x, false) in r.Items)
{
  forall x:symbol | x in r.Keys {
    x_in_r_keys(x,r);
  }
}

lemma possible_x_r_relations(r:valuation)
  ensures forall x:symbol :: x !in r.Keys || (x, true) in r.Items || (x, false) in r.Items
{
  assert forall x :: x in r.Keys || x !in r.Keys;
  x_in_r_keys_general(r);
}

lemma imp_x_nin_r(x:symbol, q:query, r:valuation)
  requires x !in r.Keys
  requires !evaluate(update_query(x,false,q), r)
  requires !evaluate(update_query(x,true,q), r)
  ensures !evaluate(q,r)
{
  evaluate_update_query(x, true, r, q);
}

lemma imp_xt_in_r(x:symbol, q:query, r:valuation)
  requires (x,true) in r.Items
  requires !evaluate(update_query(x,false,q), r)
  requires !evaluate(update_query(x,true,q), r)
  ensures !evaluate(q,r)
{
  var r' := r - {x};
  assert !evaluate(update_query(x,true,q), r');
  evaluate_update_query(x, true, r', q);
  assert !evaluate(q,r'[x:=true]);
  assert !evaluate(q,r);
}

lemma imp_xf_in_r(x:symbol, q:query, r:valuation)
  requires (x,false) in r.Items
  requires !evaluate(update_query(x,true,q), r)
  requires !evaluate(update_query(x,false,q), r)
  ensures !evaluate(q,r)
{
  var r' := r - {x};
  assert !evaluate(update_query(x,false,q), r');
  evaluate_update_query(x, false, r', q);
  assert !evaluate(q,r'[x:=false]);
  assert !evaluate(q,r);
}
// END: Helper lemmas for evaluate_update_query and simp_solve

// Updating a query under the valuation x:=b is the same as updating 
// the valuation itself and leaving the query unchanged.
lemma evaluate_update_query(x:symbol, b:bool, r:valuation, q:query)
  requires x !in r.Keys
  ensures evaluate(update_query(x,b,q), r) == evaluate(q, r[x:=b])
{
  evaluate_query_is_evaluate_clause(x, b, r[x := b], q);
  evalute_update_query_is_evaluate_udpate_clause(x, b, r, q);
  forall c | c in q
    ensures evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r)
  {
    if (x,b) in c {
      assert evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
    } else {
      if (x,!b) in c {
        if_xb_in_c_and_xnb_in_c(x, b, c, r);
        assert evaluate_clause(c, r[x:=b]) == evaluate(update_clause(x, b, c), r);
      } else {
        if_xb_nin_c_and_xnb_nin_c(x, b, r, c);
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
  ensures forall x :: x in r.Keys ==> x in symbols(q)
  decreases symbols(q)
{
  if (q == []) {
    return true, map[];
  } else if (q[0] == []) {
    return false, map[];
  } else {
    var x := q[0][0].0;

    sat, r := simp_solve(update_query(x,true,q));
    if (sat) {
      evaluate_update_query(x, true, r, q);
      r := r[x:=true];
      return;
    } 

    sat, r := simp_solve(update_query(x,false,q));
    if (sat) {
      evaluate_update_query(x, false, r, q);
      r := r[x:=false];
      return;
    }

    forall r
      ensures !evaluate(q,r)
    {
      possible_x_r_relations(r);
      if (x !in r.Keys) {
        imp_x_nin_r(x,q,r);
        assert !evaluate(q,r);
      } else if ((x,true) in r.Items) {
        imp_xt_in_r(x,q,r);
        assert !evaluate(q,r);
      } else if ((x,false) in r.Items) {
        imp_xf_in_r(x,q,r);
        assert !evaluate(q,r);
      }
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
