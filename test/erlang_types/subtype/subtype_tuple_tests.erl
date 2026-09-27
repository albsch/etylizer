-module(subtype_tuple_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

empty_tuples_edge_cases_test() ->
  S = ttuple([]),
  T = ttuple([tany()]),
  true = is_subtype(S, S),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  true = is_subtype(S, ttuple_any()),
  false = is_subtype(ttuple_any(), S),
  ok.

tuple_1_test() ->
  S = ttuple([b(a), b(b)]),
  T = ttuple([tany(), tany()]),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

tuple_2_test() ->
  S = ttuple([b(a)]),
  T = ttuple([tany(), tany()]),
  false = is_subtype(S, T),
  false = is_subtype(T, S).

empty_tuple_test() ->
  O2 = i(ttuple([b(b)]), ttuple([b(a)])),
  true = is_subtype(O2, tempty()).

simple_prod_var_test() ->
  S = ttuple([b(hello)]),
  T = ttuple([v(alpha)]),
  false = is_subtype(S, T),
  false = is_subtype(T, S).

var_prod_test() ->
  S = i(ttuple([b(hello)]), v(alpha)),
  T = v(alpha),
  true = is_subtype(S, T),
  false = is_subtype(T, S),
  ok.

neg_var_prod_test() ->
  S = ttuple([b(hello), v(alpha)]),
  T = v(alpha),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  ok.

pos_var_prod_test() ->
  S = i(ttuple([b(hello)]), v(alpha)),
  T = n(v(alpha)),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  ok.

var_subsumption_test() ->
  S = u(
    i(ttuple([b(hello)]), v(alpha)),
    ttuple([b(hello)])
  ),
  T = ttuple([b(hello)]),
  true = is_subtype(S, T),
  true = is_subtype(T, S),
  ok.

var_subsumption_2_test() ->
  S = i(
    u(
      n(ttuple([b(hello)])),
      i(ttuple([tany()]), v(beta))
    ),
    n(ttuple([b(hello)])) 
  ),
  T = n(ttuple([b(hello)])),
  true = is_subtype(S, T),
  true = is_subtype(T, S),
  ok.

var_subsumption_3_test() ->
  % alpha & !beta & SomeTuple < alpha & SomeTuple
  S = i(ttuple([b(a)]), v(alpha)),
  T = i(
    ttuple([b(a)]), 
    i(
      n(v(beta)), 
      v(alpha)
    )
  ),
  false = is_subtype(S, T),
  true = is_subtype(T, S),
  ok.

% ast_check:check_ty/5: a clause of a case over ast_erl:ty() yields the constraint
% ty() /\ not(P1 | .. | Pk) /\ {type, _, tuple, _} <: {_, _, _, $a} with about
% thirty negated 4-tuples {type, _, Tag, _}. On the line of ty()'s member
% {type, anno(), tuple, [ty()]} each of them is disjoint from BigS at the tag
% position only, so phi keeps two live branches per negated tuple. The line is
% empty, but only the last negated tuple phi sees covers it (the BDD lists the
% root atom last): every branch ends in true, nothing short-circuits, and
% without the phi memo the walk has 2^k leaves.
%
% Here the covering tuple is {type, Anno, any(), any()}: it shares the second
% component of the positive tuple, which is created before the union the negated
% patterns carry there, so it is the smallest atom of the line and phi reaches it
% last.
many_negated_tuples_test_() ->
  {timeout, 30, fun() ->
    Tags = [any, arity, atom, binary, bitstring, boolean, bounded_fun, byte, char,
            float, 'fun', integer, list, map, neg_integer, nil, no_return,
            non_neg_integer, none, nonempty_list, number, pid, port, pos_integer,
            product, range, record, reference, term],
    Fourths = [tempty_list(), tcons(tany(), tempty_list()),
               tcons(tany(), tcons(tany(), tempty_list()))],
    Anno = u([b(), tint()]),
    Pos = ttuple([b(type), Anno, b(tuple), tlist(tany())]),
    Negs = [ttuple([b(type), u([b(), tint(), tfloat()]), b(Tag), lists:nth(1 + I rem 3, Fourths)])
            || {I, Tag} <- lists:zip(lists:seq(1, length(Tags)), Tags)],
    Cover = ttuple([b(type), Anno, tany(), tany()]),
    T = ttuple([tany(), tany(), tany(), v(alpha)]),
    false = is_subtype(i([Pos, n(u(Negs))]), T),
    true = is_subtype(i([Pos, n(u(Negs ++ [Cover]))]), T)
  end}.
