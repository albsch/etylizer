-module(epike).

%% Piking: deciding the satisfiability of a tallying problem by a
%% single-path search *inside* normalization.
%%
%% Tallying (etally, v1..v6) decides "is there a solution?" in two phases
%% that both materialize every solution. Phase 1 normalizes each constraint
%% S <= T into the complete set of constraint sets that make S \ T empty --
%% bdd.hrl meets the per-line results, dnf_ty_tuple and dnf_ty_function meet
%% and join their decompositions -- and phase 2 merges those sets with meet
%% (a cartesian product pruned by subsumption), join and saturation. The
%% answer is whether the final set is non-empty; the cost is the width of
%% every intermediate set. That is how a model counter works.
%%
%% Piking never builds a set of constraint sets. "Make T empty under the
%% current bounds C" is a *goal* that is searched, one choice at a time, in
%% continuation-passing style: an AND (every DNF line, every tuple
%% component) is a chain of continuations, an OR (some component empty, some
%% negative arrow refuting the line) is a decision that backtracks, and a
%% leaf emits ONE one-sided bound -- alpha <= single(...) or single(...) <=
%% alpha, the NTLV rule -- which is merged into C on the spot. When the merge
%% tightens an existing bound, the consequence that saturation would add
%% later is itself an empty goal run right away, on the tightened pair:
%% CL \ (CU & U) (resp. (CL | L) \ CU). The search succeeds
%% when the final continuation is reached: every line consumed, every
%% consequence established, C saturated by construction. It fails when every
%% alternative is refuted. The correspondence with a SAT solver:
%%
%%   partial assignment      the bound map C : variable -> {Lower, Upper}
%%   literal                 one one-sided bound from the NTLV rule
%%   decision                an OR of the tuple or function decomposition
%%   theory propagation      the consequence goal of a tightened pair
%%   conflict                a leaf that cannot be made empty under C
%%   conflict analysis       the reason set of a failure: the decisions the
%%                           bounds it read depend on
%%   backjumping             a decision that a failure does not depend on
%%                           does not try its other alternatives
%%   learning                a goal that failed on its own, under the bounds
%%                           it read, fails at once wherever those bounds
%%                           are the same
%%   model                   the final continuation reached
%%
%% The reasons are what makes the search tractable where normalize is: a
%% tuple or function decomposition has many independent decisions, and a
%% later constraint that fails for reasons of its own must not make the
%% search enumerate their product. Every bound piece carries the decisions
%% it depends on (the path of decisions above the leaf that emitted it), a
%% consequence goal inherits the reasons of both pieces it relates, a ground
%% leaf that cannot be made empty fails with the reasons of its goal, and a
%% decision whose alternative fails for a reason it is not part of fails
%% with that reason at once.
%%
%% Learning is what makes the search not repeat itself across branches.
%% Every activation of empty(T) records the bounds it reads, first read
%% wins, and a failure carries the reads that led to it. When an activation
%% fails without its continuation ever having run, T could not be made
%% empty by itself under those reads, whatever the rest of the problem: the
%% pair {T, reads} is a nogood. Nogoods are sound under tighter bounds
%% (a failure under looser bounds is a failure under tighter ones) and are
%% reused on exact matches. The store travels with the search state and
%% comes back in failure results, so what a failed branch learned is known
%% to every later one.
%%
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded in the search
%% state and returned through the continuations: a recursive type met again
%% is assumed empty, and a sub-goal met again on the same path is skipped
%% since its bounds are already in C. Backtracking discards X with the path.
%%
%% Piking searches exactly the tree normalize + saturate materialize:
%% the same minimized lines, the same singled bounds, the same
%% decompositions, with prunings that lose no answer. A goal achieved on the
%% path is not redone (C already lies inside it, the other alternatives only
%% tighten C, and any leaf below a tighter set has a solution that also
%% satisfies C and the pending goals). A backjump skips alternatives only
%% when the failure read no bound that the decision produced, so the same
%% failure exists under every alternative. And a nogood is reused only where
%% every bound it read has the same value.

-export([is_satisfiable/2]).

-include("constraints.hrl").

-type input_constraints() :: [{ty:type(), ty:type()}].
%% The decisions a bound piece, a goal or a failure depends on.
-type reason() :: #{integer() => []}.
%% C: the bounds of every variable constrained so far, each side with the
%% decisions its pieces depend on.
-type bounds() :: #{variable() => {ty:type(), ty:type(), reason(), reason()}}.
%% X: goals achieved or assumed on the current path. {node, T} is added when
%% empty(T) starts (coinductive hypothesis) and stays; phi and explore keys
%% are added when the sub-goal completes.
-type achieved() :: #{term() => []}.
%% The bounds an activation has read, first read wins.
-type reads() :: #{variable() => {ty:type(), ty:type()}}.
%% Nogoods: the read sets under which empty(T) failed on its own.
-type store() :: #{ty:type() => [reads()]}.
-record(s, {
  c :: bounds(),
  x :: achieved(),
  reads :: reads(),
  store :: store()
}).
-type s() :: #s{}.
%% A failure names the decisions and the reads it depends on and hands back
%% what was learned; C, X and the reads of the path are discarded with it.
-type result() :: true | {false, reason(), reads(), store()}.
%% The rest of the search after a goal.
-type k() :: fun((s()) -> result()).
%% A goal runs under the decisions its existence depends on.
-type goal() :: fun((s(), k(), reason()) -> result()).

-define(NOGOODS_PER_NODE, 32).

-record(env, {
  fixed :: monomorphic_variables()
}).
-type env() :: #env{}.

-spec is_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable(Constraints, Fixed) ->
  Env = #env{fixed = Fixed},
  Goals = [empty_goal(ty_node:difference(S, T), Env) || {S, T} <- Constraints],
  S0 = #s{c = #{}, x = #{}, reads = #{}, store = #{}},
  case all_of(Goals, S0, fun(_S) -> true end, #{}) of
    true -> true;
    {false, _Reason, _Reads, _Store} -> false
  end.

%% --- combinators ------------------------------------------------------------

%% A conjunction: each goal runs with the rest of the conjunction as its
%% continuation, so a later conjunct that fails backtracks into the choices
%% of the earlier ones -- or past them, if its reason does not involve them.
-spec all_of([goal()], s(), k(), reason()) -> result().
all_of([], S, K, _Path) -> K(S);
all_of([G | Gs], S, K, Path) ->
  G(S, fun(S1) -> all_of(Gs, S1, K, Path) end, Path).

%% A disjunction: a decision. The first alternative under which the whole
%% remaining search succeeds answers the query. An alternative that fails
%% for a reason this decision is not part of fails the decision at once,
%% since the same failure exists under every other alternative; otherwise
%% the next alternative is tried with what the failed one learned, and the
%% reasons and reads of all of them are the reason the decision fails.
-spec any_of([goal()], s(), k(), reason()) -> result().
any_of([], #s{reads = Reads, store = Store}, _K, Path) -> {false, Path, Reads, Store};
any_of(Goals, S, K, Path) ->
  D = erlang:unique_integer([positive]),
  decide(Goals, S, K, Path, D, #{}, S#s.reads).

-spec decide([goal()], s(), k(), reason(), integer(), reason(), reads()) -> result().
decide([], #s{store = Store}, _K, _Path, D, Acc, Reads) -> {false, maps:remove(D, Acc), Reads, Store};
decide([G | Gs], S, K, Path, D, Acc, Reads) ->
  case G(S, K, Path#{D => []}) of
    true -> true;
    {false, R, Reads1, Store1} ->
      case R of
        #{D := _} ->
          decide(Gs, S#s{store = Store1}, K, Path, D, maps:merge(Acc, R), merge_reads(Reads, Reads1));
        _ ->
          {false, R, Reads1, Store1}
      end
  end.

-spec empty_goal(ty:type(), env()) -> goal().
empty_goal(T, Env) -> fun(S, K, Path) -> empty(T, S, K, Path, Env) end.

-spec phi_goal([ty:type()], [ty_tuple:type()], env()) -> goal().
phi_goal(BigS, Neg, Env) -> fun(S, K, Path) -> phi(BigS, Neg, S, K, Path, Env) end.

-spec explore_goal(ty:type(), ty:type(), [ty_function:type()], env()) -> goal().
explore_goal(T1, T2, P, Env) -> fun(S, K, Path) -> explore(T1, T2, P, S, K, Path, Env) end.

-spec all_goal([goal()]) -> goal().
all_goal(Goals) -> fun(S, K, Path) -> all_of(Goals, S, K, Path) end.

%% --- the variable level -----------------------------------------------------

%% Make the node T empty under C. One activation: it reads into a fresh read
%% set, hands its reads on to the continuation, and if it fails before the
%% continuation ever ran, {T, reads} is learned.
-spec empty(ty:type(), s(), k(), reason(), env()) -> result().
empty(T, S = #s{c = C, x = X, reads = Reads0, store = Store0}, K, Path, Env = #env{fixed = Fixed}) ->
  case X of
    #{{node, T} := _} -> K(S);
    _ ->
      Lines = ground_first(dnf_ty_variable:minimize_dnf(ty_node:load(T)), Fixed),
      Goals = [fun(S1, K2, P1) -> line(L, S1, K2, P1, Env) end || L <- Lines],
      case known_failure(T, C, Store0, Env) of
        {true, Reads} ->
          {false, maps:merge(Path, reason_of(Reads, C)), merge_reads(Reads0, Reads), Store0};
        false ->
          Tok = erlang:unique_integer([positive]),
          K1 = fun(S1 = #s{reads = ReadsIn}) ->
                 case K(S1#s{reads = merge_reads(Reads0, ReadsIn)}) of
                   true -> true;
                   {false, R, Rd, St} -> {false, R#{Tok => []}, Rd, St}
                 end
               end,
          case all_of(Goals, S#s{x = X#{{node, T} => []}, reads = #{}}, K1, Path) of
            true -> true;
            {false, R, ReadsIn, St} ->
              case R of
                #{Tok := _} ->
                  {false, maps:remove(Tok, R), ReadsIn, St};
                _ ->
                  {false, R, merge_reads(Reads0, ReadsIn), learn(T, ReadsIn, St)}
              end
          end
      end
  end.

%% Lines without a polymorphic variable go first: they are the only ones that
%% can fail on their own, and a variable line only emits a bound.
-spec ground_first([L], monomorphic_variables()) -> [L] when L :: {[variable()], [variable()], ty_rec:type()}.
ground_first(Lines, Fixed) ->
  {Ground, Poly} = lists:partition(
    fun({P, N, _}) -> lists:all(fun(V) -> maps:is_key(V, Fixed) end, P ++ N) end, Lines),
  Ground ++ Poly.

%% One DNF line of the variable BDD: alpha_1 & .. & !beta_1 & .. & Leaf <= 0.
%% The NTLV rule singles out the smallest polymorphic variable into one
%% one-sided bound; a line without one is the leaf's problem.
-spec line({[variable()], [variable()], ty_rec:type()}, s(), k(), reason(), env()) -> result().
line({[], [], Leaf}, S, K, Path, Env) ->
  leaf_empty(Leaf, S, K, Path, Env);
line({P, N, Leaf}, S, K, Path, Env = #env{fixed = Fixed}) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} ->
      U = ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf)),
      bound_upper(V, U, S, K, Path, Env);
    {{neg, V}, _} ->
      L = ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf)),
      bound_lower(V, L, S, K, Path, Env);
    {{{delta, _}, _}, _} ->
      % only monomorphic variables: they are eliminated (Part 1, Lemma C.3/C.11)
      leaf_empty(Leaf, S, K, Path, Env)
  end.

%% alpha <= U, a piece depending on Path. Tightening an existing upper bound
%% obliges the lower bound to fit under the tightened bound: CL <= U1, an
%% empty goal on CL \ U1 that depends on the reasons of both whole sides.
%% Both current bounds are read.
-spec bound_upper(variable(), ty:type(), s(), k(), reason(), env()) -> result().
bound_upper(V, U, S = #s{c = C, reads = Reads}, K, Path, Env) ->
  Empty = ty_node:empty(),
  Any = ty_node:any(),
  case C of
    #{V := {CL, CU, RL, RU}} ->
      S1 = S#s{reads = read(V, CL, CU, Reads)},
      case intersect_bound(U, CU, Env) of
        CU -> K(S1);
        U1 ->
          S2 = S1#s{c = C#{V := {CL, U1, RL, maps:merge(RU, Path)}}},
          case CL of
            Empty -> K(S2);
            _ ->
              empty(ty_node:difference(CL, U1), S2, K, maps:merge(RL, maps:merge(RU, Path)), Env)
          end
      end;
    _ ->
      K(S#s{c = C#{V => {Empty, U, #{}, Path}}, reads = read(V, Empty, Any, Reads)})
  end.

%% L <= alpha, symmetric: the whole lower bound must fit under the upper bound.
-spec bound_lower(variable(), ty:type(), s(), k(), reason(), env()) -> result().
bound_lower(V, L, S = #s{c = C, reads = Reads}, K, Path, Env) ->
  Empty = ty_node:empty(),
  Any = ty_node:any(),
  case C of
    #{V := {CL, CU, RL, RU}} ->
      S1 = S#s{reads = read(V, CL, CU, Reads)},
      case union_bound(L, CL, Env) of
        CL -> K(S1);
        L1 ->
          S2 = S1#s{c = C#{V := {L1, CU, maps:merge(RL, Path), RU}}},
          case CU of
            Any -> K(S2);
            _ ->
              empty(ty_node:difference(L1, CU), S2, K, maps:merge(RU, maps:merge(RL, Path)), Env)
          end
      end;
    _ ->
      K(S#s{c = C#{V => {L, Any, Path, #{}}}, reads = read(V, Empty, Any, Reads)})
  end.

%% --- learning ---------------------------------------------------------------


%% First read wins: the value an activation saw first is the one its
%% outcome depends on; later, tighter values are its own doing.
-spec read(variable(), ty:type(), ty:type(), reads()) -> reads().
read(V, L, U, Reads) ->
  case Reads of
    #{V := _} -> Reads;
    _ -> Reads#{V => {L, U}}
  end.

%% The reads of an enclosing activation, extended by those of a nested one.
-spec merge_reads(reads(), reads()) -> reads().
merge_reads(Older, Newer) -> maps:merge(Newer, Older).

-spec learn(ty:type(), reads(), store()) -> store().
learn(T, Reads, Store) ->
  Known = maps:get(T, Store, []),
  Store#{T => lists:sublist([Reads | Known], ?NOGOODS_PER_NODE)}.

%% A nogood applies when every bound it read has the same value now.
-spec known_failure(ty:type(), bounds(), store(), env()) -> false | {true, reads()}.
known_failure(T, C, Store, _Env) ->
  Empty = ty_node:empty(),
  Any = ty_node:any(),
  case Store of
    #{T := Nogoods} ->
      Matches = fun(Reads) ->
        lists:all(
          fun({V, {L, U}}) ->
            case C of
              #{V := {CL, CU, _, _}} -> CL =:= L andalso CU =:= U;
              _ -> L =:= Empty andalso U =:= Any
            end
          end, maps:to_list(Reads))
      end,
      case lists:search(Matches, Nogoods) of
        {value, Reads} -> {true, Reads};
        false -> false
      end;
    _ -> false
  end.

%% The decisions the current values of the read bounds depend on. A hit adds
%% the path of the goal itself: the failure also depends on the decisions
%% that posed the goal.
-spec reason_of(reads(), bounds()) -> reason().
reason_of(Reads, C) ->
  maps:fold(
    fun(V, _, Acc) ->
      case C of
        #{V := {_, _, RL, RU}} -> maps:merge(Acc, maps:merge(RL, RU));
        _ -> Acc
      end
    end, #{}, Reads).

%% --- the leaf level ---------------------------------------------------------

%% A variable-free line is empty iff every component of its leaf is. The
%% basic kinds are decided outright; the structured kinds are searched.
-spec leaf_empty(ty_rec:type(), s(), k(), reason(), env()) -> result().
leaf_empty(any, #s{reads = Reads, store = Store}, _K, Path, _Env) -> {false, Path, Reads, Store};
leaf_empty(empty, S, K, _Path, _Env) -> K(S);
leaf_empty(TyRec, S = #s{reads = Reads, store = Store}, K, Path, Env) ->
  case basic_empty(TyRec) of
    false -> {false, Path, Reads, Store};
    true ->
      {TupDefault, TupArities} = ty_rec:pi(TyRec, ty_tuples),
      {FunDefault, FunArities} = ty_rec:pi(TyRec, ty_functions),
      Goals =
        tuple_goals(dnf_ty_list:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_list)), Env) ++
        tuple_goals(dnf_ty_bitstring:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_bitstring)), Env) ++
        lists:append([tuple_goals(dnf_ty_tuple:minimize_dnf(D), Env)
                      || {_Arity, D} <- lists:sort(maps:to_list(TupArities))]) ++
        tuple_goals(dnf_ty_tuple:minimize_dnf(TupDefault), Env) ++
        lists:append([function_goals(dnf_ty_function:minimize_dnf(D), Env)
                      || {_Arity, D} <- lists:sort(maps:to_list(FunArities))]) ++
        function_goals(dnf_ty_function:minimize_dnf(FunDefault), Env) ++
        map_goals(dnf_ty_map:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_map)), Env),
      all_of(Goals, S, K, Path)
  end.

-spec basic_empty(ty_rec:type_record()) -> boolean().
basic_empty(TyRec) ->
  element(1, dnf_ty_predefined:is_empty(ty_rec:pi(TyRec, dnf_ty_predefined), #{}))
    andalso element(1, dnf_ty_atom:is_empty(ty_rec:pi(TyRec, dnf_ty_atom), #{}))
    andalso element(1, dnf_ty_interval:is_empty(ty_rec:pi(TyRec, dnf_ty_interval), #{})).

-spec tuple_goals([{[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}], env()) -> [goal()].
tuple_goals(Lines, Env) ->
  [fun(S, K, Path) -> tuple_line(L, S, K, Path, Env) end || L <- Lines].

-spec function_goals([{[ty_function:type()], [ty_function:type()], ty_bool:type()}], env()) -> [goal()].
function_goals(Lines, Env) ->
  [fun(S, K, Path) -> function_line(L, S, K, Path, Env) end || L <- Lines].

-spec map_goals([{[ty_map:type()], [ty_map:type()], ty_bool:type()}], env()) -> [goal()].
map_goals(Lines, Env) ->
  [fun(S, K, Path) -> map_line(L, S, K, Path, Env) end || L <- Lines].

%% One line of a tuple (or list, bitstring) DNF, as dnf_ty_tuple:normalize_line.
-spec tuple_line({[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}, s(), k(), reason(), env()) -> result().
tuple_line({[], [], _}, #s{reads = Reads, store = Store}, _K, Path, _Env) ->
  {false, Path, Reads, Store}; % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, S, K, Path, Env) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, S, K, Path, Env);
tuple_line({Pos, Neg, _}, S, K, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, S, K, Path, Env).

%% One line of a map DNF, as dnf_ty_map:normalize_line: maps are encoded as a
%% pair of a tuple part and a function part, with its own any.
-spec map_line({[ty_map:type()], [ty_map:type()], ty_bool:type()}, s(), k(), reason(), env()) -> result().
map_line({[], [], _}, #s{reads = Reads, store = Store}, _K, Path, _Env) -> {false, Path, Reads, Store};
map_line({[], Neg = [_ | _], Leaf}, S, K, Path, Env) ->
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  map_line({[ty_map:map(P1, P2)], Neg, Leaf}, S, K, Path, Env);
map_line({Pos, Neg, _}, S, K, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, S, K, Path, Env).

%% S1 x .. x Sn \ (N1 | .. | Nk) <= 0, as dnf_ty_tuple:phi_norm: some Si is
%% empty, or for the first negative tuple N1, for every component i the
%% product with Si \ N1_i is empty without N1. One decision, unless a
%% component is already empty on this path.
-spec phi([ty:type()], [ty_tuple:type()], s(), k(), reason(), env()) -> result().
phi(BigS, Neg, S = #s{x = X}, K, Path, Env) ->
  Key = {phi, BigS, Neg},
  case X of
    #{Key := _} -> K(S);
    _ ->
      K1 = fun(S1 = #s{x = X1}) -> K(S1#s{x = X1#{Key => []}}) end,
      case lists:any(fun(Si) -> maps:is_key({node, Si}, X) end, BigS) of
        true -> K1(S);
        false ->
          Components = [empty_goal(Si, Env) || Si <- BigS],
          Alternatives = case Neg of
            [] -> Components;
            [Ty | N] -> Components ++ [all_goal(without(BigS, ty_tuple:components(Ty), 1, N, Env))]
          end,
          any_of(Alternatives, S, K1, Path)
      end
  end.

-spec without([ty:type()], [ty:type()], pos_integer(), [ty_tuple:type()], env()) -> [goal()].
without(_BigS, [], _I, _N, _Env) -> [];
without(BigS, [NComp | Rest], I, N, Env) ->
  [phi_goal(replace_at(I, BigS, NComp), N, Env) | without(BigS, Rest, I + 1, N, Env)].

-spec replace_at(pos_integer(), [ty:type()], ty:type()) -> [ty:type()].
replace_at(1, [H | T], NComp) -> [ty_node:difference(H, NComp) | T];
replace_at(I, [H | T], NComp) -> [H | replace_at(I - 1, T, NComp)].

%% One line of a function DNF, as dnf_ty_function:normalize_line: some
%% negative arrow T1 -> T2 refutes the intersection of the positive arrows,
%% which needs T1 inside the union S of the domains and explore to hold.
%% Which negative arrow is one decision.
-spec function_line({[ty_function:type()], [ty_function:type()], ty_bool:type()}, s(), k(), reason(), env()) -> result().
function_line({Pos, Neg, _}, S, K, Path, Env) ->
  Dom = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  NotDom = ty_node:negate(Dom),
  Alternatives =
    [all_goal([empty_goal(ty_node:intersect(ty_function:domain(F), NotDom), Env),
               explore_goal(ty_function:domain(F), ty_node:negate(ty_function:codomain(F)), Pos, Env)])
     || F <- Neg],
  any_of(Alternatives, S, K, Path).

%% As dnf_ty_function:explore_function_norm: T1 empty, or T2 empty, or the
%% positive arrow S1 -> S2 is split off on both sides. One decision, unless
%% T1 or T2 is already empty on this path.
-spec explore(ty:type(), ty:type(), [ty_function:type()], s(), k(), reason(), env()) -> result().
explore(T1, T2, [], S, K, Path, Env) ->
  any_of([empty_goal(T1, Env), empty_goal(T2, Env)], S, K, Path);
explore(T1, T2, P = [F | Ps], S = #s{x = X}, K, Path, Env) ->
  Key = {explore, T1, T2, P},
  case X of
    #{Key := _} -> K(S);
    _ ->
      K1 = fun(S1 = #s{x = X1}) -> K(S1#s{x = X1#{Key => []}}) end,
      case maps:is_key({node, T1}, X) orelse maps:is_key({node, T2}, X) of
        true -> K1(S);
        false ->
          S1 = ty_function:domain(F),
          S2 = ty_function:codomain(F),
          any_of([empty_goal(T1, Env),
                  empty_goal(T2, Env),
                  all_goal([explore_goal(T1, ty_node:intersect(T2, S2), Ps, Env),
                            explore_goal(ty_node:difference(T1, S1), T2, Ps, Env)])],
                 S, K1, Path)
      end
  end.

%% --- bounds -----------------------------------------------------------------

%% Identical nodes need no engine call; the empty and any nodes are units.
-spec union_bound(T, T, env()) -> T when T :: ty:type().
union_bound(A, A, _Env) -> A;
union_bound(A, B, _Env) ->
  case ty_node:empty() of
    A -> B;
    B -> A;
    _ -> ty_node:union(A, B)
  end.

-spec intersect_bound(T, T, env()) -> T when T :: ty:type().
intersect_bound(A, A, _Env) -> A;
intersect_bound(A, B, _Env) ->
  case ty_node:any() of
    A -> B;
    B -> A;
    _ -> ty_node:intersect(A, B)
  end.
