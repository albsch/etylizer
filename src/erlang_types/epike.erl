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
%% current bounds C" is a *goal* that is searched, one choice at a time, by
%% an iterative engine over two stacks: an AND (every DNF line, every tuple
%% component) pushes the rest of the conjunction onto the continuation
%% stack K, an OR (some component empty, some negative arrow refuting the
%% line) is a choice point that pushes its remaining alternatives onto the
%% trail and backtracks, and a leaf emits ONE one-sided bound -- alpha <=
%% single(...) or single(...) <= alpha, the NTLV rule -- which is merged
%% into C on the spot. When the merge tightens an existing bound, the
%% consequence that saturation would add later is itself an empty goal run
%% right away, on the tightened pair: CL \ (CU & U) (resp. (CL | L) \ CU).
%% The search succeeds when K is exhausted: every line consumed, every
%% consequence established, C saturated by construction. It fails when the
%% trail is: every alternative refuted. The correspondence with a SAT
%% solver:
%%
%%   partial assignment      the bound map C : variable -> {Lower, Upper}
%%   literal                 one one-sided bound from the NTLV rule
%%   clause / decision       an OR of the tuple or function decomposition
%%   theory propagation      the consequence goal of a tightened pair
%%   conflict                a leaf that cannot be made empty under C
%%   model                   K exhausted
%%
%% The engine. Goals are data, and the search is three mutually
%% tail-recursive functions, so it runs in constant Erlang stack however
%% deep the path:
%%
%%   goal/6   runs a goal under the current bounds and achieved set
%%   ret/5    the goal succeeded: the next frame of K runs -- the remaining
%%            conjuncts of an enclosing conjunction
%%   fail/2   the goal failed: the latest choice point on the trail tries
%%            its next alternative
%%
%% A frame of K is what a continuation closes over, and the trail is the
%% call stack a failure returns through in continuation-passing style: a
%% choice point for every OR on the path, with the alternatives it has
%% left. A choice point keeps the bounds, the achieved set and K it was
%% made under, so its next alternative starts from them; K is a list,
%% shared by every alternative.
%%
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded as an argument
%% along K: a recursive type met again is assumed empty, and a sub-goal met
%% again on the same path is skipped since its bounds are already in C.
%% Backtracking discards X with the path.
%%
%% Piking searches exactly the tree normalize + saturate materialize:
%% the same minimized lines, the same singled bounds, the same
%% decompositions in the same order, with one pruning that loses no answer.
%% A goal achieved on the path is not redone (C already lies inside it, the
%% other alternatives only tighten C, and any leaf below a tighter set has a
%% solution that also satisfies C and the pending goals).

-export([is_satisfiable/2]).

-include("constraints.hrl").

-type input_constraints() :: [{ty:type(), ty:type()}].
%% C: the current bounds of every variable constrained so far.
-type bounds() :: #{variable() => {ty:type(), ty:type()}}.
%% X: goals achieved or assumed on the current path. {node, T} is added when
%% empty(T) starts (coinductive hypothesis) and stays.
-type achieved() :: #{term() => []}.

%% A goal.
-type goal() :: {empty, ty:type()}                             % make the node empty
              | {line, {[variable()], [variable()], ty_rec:type()}} % a DNF line of a node
              | {all, [goal()]}                                % a conjunction
              | {phi, [ty:type()], [ty_tuple:type()]}
              | {without, [ty:type()], ty_tuple:type(), [ty_tuple:type()]} % phi without a negative tuple
              | {explore, ty:type(), ty:type(), [ty_function:type()]}
              | {split, ty:type(), ty:type(), ty_function:type(), [ty_function:type()]} % explore splitting an arrow off
              | {refute, ty:type(), [ty_function:type()], ty_function:type()} % a negative arrow refuting a line
              | component().
%% K, the rest of the search after a goal, innermost frame first.
-type frame() :: {conj, [goal(), ...]}.                % the conjuncts left
-type k() :: [frame()].
%% The trail: the choice points of the path, innermost first.
-type handler() :: {choice, [goal()], bounds(), achieved(), k()}. % a choice point: alternatives left, its state
-type trail() :: [handler()].

-record(env, {
  fixed :: monomorphic_variables()
}).
-type env() :: #env{}.

-spec is_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable(Constraints, Fixed) ->
  Env = #env{fixed = Fixed},
  Goals = [{empty, ty_node:difference(S, T)} || {S, T} <- Constraints],
  all_of(Goals, #{}, #{}, [], [], Env).

%% --- the engine -------------------------------------------------------------

%% Run a goal.
-spec goal(goal(), bounds(), achieved(), k(), trail(), env()) -> boolean().
goal({empty, T}, C, X, K, Tr, Env) ->
  empty(T, C, X, K, Tr, Env);
goal({all, Goals}, C, X, K, Tr, Env) ->
  all_of(Goals, C, X, K, Tr, Env);
goal({phi, BigS, Neg}, C, X, K, Tr, Env) ->
  phi(BigS, Neg, C, X, K, Tr, Env);
goal({without, BigS, Ty, N}, C, X, K, Tr, Env) ->
  all_of(without(BigS, ty_tuple:components(Ty), 1, N), C, X, K, Tr, Env);
goal({explore, T1, T2, P}, C, X, K, Tr, Env) ->
  explore(T1, T2, P, C, X, K, Tr, Env);
goal({split, T1, T2, F, Ps}, C, X, K, Tr, Env) ->
  split(T1, T2, F, Ps, C, X, K, Tr, Env);
goal({refute, S, P, F}, C, X, K, Tr, Env) ->
  refute(S, P, F, C, X, K, Tr, Env);
goal({line, L}, C, X, K, Tr, Env) ->
  line(L, C, X, K, Tr, Env);
goal({tuple, L}, C, X, K, Tr, Env) ->
  tuple_line(L, C, X, K, Tr, Env);
goal({function, L}, C, X, K, Tr, Env) ->
  function_line(L, C, X, K, Tr, Env);
goal({map, L}, C, X, K, Tr, Env) ->
  map_line(L, C, X, K, Tr, Env).

%% The goal succeeded: the next frame of K runs, and the search succeeds
%% when there is none.
-spec ret(bounds(), achieved(), k(), trail(), env()) -> boolean().
ret(_C, _X, [], _Tr, _Env) -> true;
ret(C, X, [{conj, Goals} | K], Tr, Env) ->
  all_of(Goals, C, X, K, Tr, Env).

%% The search failed: the latest choice point on the trail tries its next
%% alternative, and the search fails when there is none.
-spec fail(trail(), env()) -> boolean().
fail([], _Env) -> false;
fail([{choice, Goals, C, X, K} | Tr], Env) ->
  any_of(Goals, C, X, K, Tr, Env).

%% A conjunction: each goal runs with the rest of the conjunction on K, so a
%% later conjunct that fails backtracks into the choices of the earlier
%% ones.
-spec all_of([goal()], bounds(), achieved(), k(), trail(), env()) -> boolean().
all_of([], C, X, K, Tr, Env) -> ret(C, X, K, Tr, Env);
all_of([G | Gs], C, X, K, Tr, Env) ->
  K1 = case Gs of [] -> K; _ -> [{conj, Gs} | K] end,
  goal(G, C, X, K1, Tr, Env).

%% A disjunction: a choice point. The first alternative under which the
%% whole remaining search succeeds answers the query.
-spec any_of([goal()], bounds(), achieved(), k(), trail(), env()) -> boolean().
any_of([], _C, _X, _K, Tr, Env) -> fail(Tr, Env);
any_of([G | Gs], C, X, K, Tr, Env) ->
  goal(G, C, X, K, [{choice, Gs, C, X, K} | Tr], Env).

%% --- the variable level -----------------------------------------------------

%% Make the node T empty under C.
-spec empty(ty:type(), bounds(), achieved(), k(), trail(), env()) -> boolean().
empty(T, C, X, K, Tr, Env) ->
  case X of
    #{{node, T} := _} -> ret(C, X, K, Tr, Env);
    _ ->
      Lines = dnf_ty_variable:minimize_dnf(ty_node:load(T)),
      all_of([{line, L} || L <- Lines], C, X#{{node, T} => []}, K, Tr, Env)
  end.

%% One DNF line of the variable BDD: alpha_1 & .. & !beta_1 & .. & Leaf <= 0.
%% The NTLV rule singles out the smallest polymorphic variable into one
%% one-sided bound; a line without one is the leaf's problem.
-spec line({[variable()], [variable()], ty_rec:type()}, bounds(), achieved(), k(), trail(), env()) -> boolean().
line({[], [], Leaf}, C, X, K, Tr, Env) ->
  leaf_empty(Leaf, C, X, K, Tr, Env);
line({P, N, Leaf}, C, X, K, Tr, Env = #env{fixed = Fixed}) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} ->
      U = ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf)),
      bound_upper(V, U, C, X, K, Tr, Env);
    {{neg, V}, _} ->
      L = ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf)),
      bound_lower(V, L, C, X, K, Tr, Env);
    {{{delta, _}, _}, _} ->
      % only monomorphic variables: they are eliminated (Part 1, Lemma C.3/C.11)
      leaf_empty(Leaf, C, X, K, Tr, Env)
  end.

%% alpha <= U. Tightening an existing upper bound obliges the lower bound to
%% fit under the tightened bound: CL <= U1, an empty goal on CL \ U1.
-spec bound_upper(variable(), ty:type(), bounds(), achieved(), k(), trail(), env()) -> boolean().
bound_upper(V, U, C, X, K, Tr, Env) ->
  Empty = ty_node:empty(),
  case C of
    #{V := {CL, CU}} ->
      case intersect_bound(U, CU, Env) of
        CU -> ret(C, X, K, Tr, Env);
        U1 ->
          C1 = C#{V := {CL, U1}},
          case CL of
            Empty -> ret(C1, X, K, Tr, Env);
            _ ->
              empty(ty_node:difference(CL, U1), C1, X, K, Tr, Env)
          end
      end;
    _ ->
      ret(C#{V => {Empty, U}}, X, K, Tr, Env)
  end.

%% L <= alpha, symmetric: the whole lower bound must fit under the upper bound.
-spec bound_lower(variable(), ty:type(), bounds(), achieved(), k(), trail(), env()) -> boolean().
bound_lower(V, L, C, X, K, Tr, Env) ->
  Any = ty_node:any(),
  case C of
    #{V := {CL, CU}} ->
      case union_bound(L, CL, Env) of
        CL -> ret(C, X, K, Tr, Env);
        L1 ->
          C1 = C#{V := {L1, CU}},
          case CU of
            Any -> ret(C1, X, K, Tr, Env);
            _ ->
              empty(ty_node:difference(L1, CU), C1, X, K, Tr, Env)
          end
      end;
    _ ->
      ret(C#{V => {L, Any}}, X, K, Tr, Env)
  end.

%% --- the leaf level ---------------------------------------------------------

%% A variable-free line is empty iff every component of its leaf is. The
%% basic kinds are decided outright; the structured kinds are searched, each
%% line of their DNFs a goal.
-type component() :: {tuple, tuple_dnf_line()} | {function, function_dnf_line()} | {map, map_dnf_line()}.
-type tuple_dnf_line() :: {[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}.
-type function_dnf_line() :: {[ty_function:type()], [ty_function:type()], ty_bool:type()}.
-type map_dnf_line() :: {[ty_map:type()], [ty_map:type()], ty_bool:type()}.
-spec leaf_empty(ty_rec:type(), bounds(), achieved(), k(), trail(), env()) -> boolean().
leaf_empty(any, _C, _X, _K, Tr, Env) -> fail(Tr, Env);
leaf_empty(empty, C, X, K, Tr, Env) -> ret(C, X, K, Tr, Env);
leaf_empty(TyRec, C, X, K, Tr, Env) ->
  case basic_empty(TyRec) of
    false -> fail(Tr, Env);
    true ->
      {TupDefault, TupArities} = ty_rec:pi(TyRec, ty_tuples),
      {FunDefault, FunArities} = ty_rec:pi(TyRec, ty_functions),
      Components =
        [{tuple, L} || L <- dnf_ty_list:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_list))] ++
        [{tuple, L} || L <- dnf_ty_bitstring:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_bitstring))] ++
        [{tuple, L} || {_Arity, D} <- lists:sort(maps:to_list(TupArities)), L <- dnf_ty_tuple:minimize_dnf(D)] ++
        [{tuple, L} || L <- dnf_ty_tuple:minimize_dnf(TupDefault)] ++
        [{function, L} || {_Arity, D} <- lists:sort(maps:to_list(FunArities)), L <- dnf_ty_function:minimize_dnf(D)] ++
        [{function, L} || L <- dnf_ty_function:minimize_dnf(FunDefault)] ++
        [{map, L} || L <- dnf_ty_map:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_map))],
      all_of(Components, C, X, K, Tr, Env)
  end.

-spec basic_empty(ty_rec:type_record()) -> boolean().
basic_empty(TyRec) ->
  element(1, dnf_ty_predefined:is_empty(ty_rec:pi(TyRec, dnf_ty_predefined), #{}))
    andalso element(1, dnf_ty_atom:is_empty(ty_rec:pi(TyRec, dnf_ty_atom), #{}))
    andalso element(1, dnf_ty_interval:is_empty(ty_rec:pi(TyRec, dnf_ty_interval), #{})).

%% One line of a tuple (or list, bitstring) DNF, as dnf_ty_tuple:normalize_line.
-spec tuple_line(tuple_dnf_line(), bounds(), achieved(), k(), trail(), env()) -> boolean().
tuple_line({[], [], _}, _C, _X, _K, Tr, Env) -> fail(Tr, Env); % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, C, X, K, Tr, Env) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, C, X, K, Tr, Env);
tuple_line({Pos, Neg, _}, C, X, K, Tr, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, C, X, K, Tr, Env).

%% One line of a map DNF, as dnf_ty_map:normalize_line: maps are encoded as a
%% pair of a tuple part and a function part, with its own any.
-spec map_line(map_dnf_line(), bounds(), achieved(), k(), trail(), env()) -> boolean().
map_line({[], [], _}, _C, _X, _K, Tr, Env) -> fail(Tr, Env);
map_line({[], Neg = [_ | _], Leaf}, C, X, K, Tr, Env) ->
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  map_line({[ty_map:map(P1, P2)], Neg, Leaf}, C, X, K, Tr, Env);
map_line({Pos, Neg, _}, C, X, K, Tr, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, C, X, K, Tr, Env).

%% S1 x .. x Sn \ (N1 | .. | Nk) <= 0, as dnf_ty_tuple:phi_norm: some Si is
%% empty, or for the first negative tuple N1, for every component i the
%% product with Si \ N1_i is empty without N1.
-spec phi([ty:type()], [ty_tuple:type()], bounds(), achieved(), k(), trail(), env()) -> boolean().
phi(BigS, Neg, C, X, K, Tr, Env) ->
  Components = [{empty, S} || S <- BigS],
  case Neg of
    [] -> any_of(Components, C, X, K, Tr, Env);
    [Ty | N] -> any_of(Components ++ [{without, BigS, Ty, N}], C, X, K, Tr, Env)
  end.

-spec without([ty:type()], [ty:type()], pos_integer(), [ty_tuple:type()]) -> [goal()].
without(_BigS, [], _I, _N) -> [];
without(BigS, [NComp | Rest], I, N) ->
  [{phi, replace_at(I, BigS, NComp), N} | without(BigS, Rest, I + 1, N)].

-spec replace_at(pos_integer(), [ty:type()], ty:type()) -> [ty:type()].
replace_at(1, [H | T], NComp) -> [ty_node:difference(H, NComp) | T];
replace_at(I, [H | T], NComp) -> [H | replace_at(I - 1, T, NComp)].

%% One line of a function DNF, as dnf_ty_function:normalize_line: some
%% negative arrow T1 -> T2 refutes the intersection of the positive arrows,
%% which needs T1 inside the union S of the domains and explore to hold.
-spec function_line(function_dnf_line(), bounds(), achieved(), k(), trail(), env()) -> boolean().
function_line({Pos, Neg, _}, C, X, K, Tr, Env) ->
  S = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  % no negative arrow: never empty
  any_of([{refute, S, Pos, F} || F <- Neg], C, X, K, Tr, Env).

-spec refute(ty:type(), [ty_function:type()], ty_function:type(), bounds(), achieved(), k(), trail(), env()) -> boolean().
refute(S, P, F, C, X, K, Tr, Env) ->
  T1 = ty_function:domain(F),
  T2 = ty_function:codomain(F),
  all_of([{empty, ty_node:intersect(T1, ty_node:negate(S))},
          {explore, T1, ty_node:negate(T2), P}], C, X, K, Tr, Env).

%% As dnf_ty_function:explore_function_norm: T1 empty, or T2 empty, or the
%% positive arrow S1 -> S2 is split off on both sides.
-spec explore(ty:type(), ty:type(), [ty_function:type()], bounds(), achieved(), k(), trail(), env()) -> boolean().
explore(T1, T2, [], C, X, K, Tr, Env) ->
  any_of([{empty, T1}, {empty, T2}], C, X, K, Tr, Env);
explore(T1, T2, [F | Ps], C, X, K, Tr, Env) ->
  any_of([{empty, T1}, {empty, T2}, {split, T1, T2, F, Ps}], C, X, K, Tr, Env).

-spec split(ty:type(), ty:type(), ty_function:type(), [ty_function:type()], bounds(), achieved(), k(), trail(), env()) -> boolean().
split(T1, T2, F, Ps, C, X, K, Tr, Env) ->
  S1 = ty_function:domain(F),
  S2 = ty_function:codomain(F),
  all_of([{explore, T1, ty_node:intersect(T2, S2), Ps},
          {explore, ty_node:difference(T1, S1), T2, Ps}], C, X, K, Tr, Env).

%% --- bounds -----------------------------------------------------------------

-spec union_bound(T, T, env()) -> T when T :: ty:type().
union_bound(A, B, _Env) -> ty_node:union(A, B).

-spec intersect_bound(T, T, env()) -> T when T :: ty:type().
intersect_bound(A, B, _Env) -> ty_node:intersect(A, B).
