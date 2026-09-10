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
%% later is itself an empty goal run right away: only the *incremental* part
%% CL \ U (resp. L \ CU), never the accumulated pair. The search succeeds
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
%% Ground goals -- types whose variables are all monomorphic -- are decided
%% by the subtyping engine (ty_node:is_empty, cached in ETS), never walked.
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded as an argument
%% and returned through the continuations: a recursive type met again is
%% assumed empty, and a sub-goal met again on the same path is skipped since
%% its bounds are already in C. Backtracking discards X with the path.
%%
%% Piking searches exactly the tree normalize + saturate materialize:
%% the same minimized lines, the same singled bounds, the same
%% decompositions, with prunings that lose no answer. A goal achieved on the
%% path is not redone (C already lies inside it, the other alternatives only
%% tighten C, and any leaf below a tighter set has a solution that also
%% satisfies C and the pending goals). The consequence of a tightened pair is
%% its incremental part: every pair (lower piece, upper piece) is covered
%% when the later of the two arrives. And a backjump skips alternatives only
%% when the failure read no bound that the decision produced, so the same
%% failure exists under every alternative.

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
-type result() :: true | {false, reason()}.
%% The rest of the search after a goal: takes the bounds and achieved set
%% the goal produced, returns whether the whole remaining search succeeds
%% and, if not, why.
-type k() :: fun((bounds(), achieved()) -> result()).
%% A goal runs under the decisions its existence depends on.
-type goal() :: fun((bounds(), achieved(), k(), reason()) -> result()).

-record(env, {
  fixed :: monomorphic_variables(),
  empty :: ty:type(),
  any :: ty:type(),
  stats :: boolean()
}).
-type env() :: #env{}.

-spec is_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable(Constraints, Fixed) ->
  Env = #env{fixed = Fixed, empty = ty_node:empty(), any = ty_node:any(),
             stats = os:getenv("PIKE_STATS") =/= false},
  stats_start(Env),
  Goals = [empty_goal(ty_node:difference(S, T), Env) || {S, T} <- Constraints],
  Result = case all_of(Goals, #{}, #{}, fun(_C, _X) -> true end, #{}) of
    true -> true;
    {false, _Reason} -> false
  end,
  stats_stop(Env, length(Constraints), Result),
  Result.

%% --- combinators ------------------------------------------------------------

%% A conjunction: each goal runs with the rest of the conjunction as its
%% continuation, so a later conjunct that fails backtracks into the choices
%% of the earlier ones -- or past them, if its reason does not involve them.
-spec all_of([goal()], bounds(), achieved(), k(), reason()) -> result().
all_of([], C, X, K, _Path) -> K(C, X);
all_of([G | Gs], C, X, K, Path) ->
  G(C, X, fun(C1, X1) -> all_of(Gs, C1, X1, K, Path) end, Path).

%% A disjunction: a decision. The first alternative under which the whole
%% remaining search succeeds answers the query. An alternative that fails
%% for a reason this decision is not part of fails the decision at once,
%% since the same failure exists under every other alternative; otherwise
%% the next alternative is tried, and the reasons of all of them, minus the
%% decision itself, are the reason the decision fails.
-spec any_of([goal()], bounds(), achieved(), k(), reason()) -> result().
any_of([], _C, _X, _K, Path) -> {false, Path};
any_of(Goals, C, X, K, Path) ->
  D = erlang:unique_integer([positive]),
  decide(Goals, C, X, K, Path, D, #{}).

-spec decide([goal()], bounds(), achieved(), k(), reason(), integer(), reason()) -> result().
decide([], _C, _X, _K, _Path, D, Acc) -> {false, maps:remove(D, Acc)};
decide([G | Gs], C, X, K, Path, D, Acc) ->
  case G(C, X, K, Path#{D => []}) of
    true -> true;
    {false, R} ->
      case R of
        #{D := _} ->
          bump(backtracks),
          decide(Gs, C, X, K, Path, D, maps:merge(Acc, R));
        _ ->
          bump(backjumps),
          {false, R}
      end
  end.

-spec empty_goal(ty:type(), env()) -> goal().
empty_goal(T, Env) -> fun(C, X, K, Path) -> empty(T, C, X, K, Path, Env) end.

-spec phi_goal([ty:type()], [ty_tuple:type()], env()) -> goal().
phi_goal(BigS, Neg, Env) -> fun(C, X, K, Path) -> phi(BigS, Neg, C, X, K, Path, Env) end.

-spec explore_goal(ty:type(), ty:type(), [ty_function:type()], env()) -> goal().
explore_goal(T1, T2, P, Env) -> fun(C, X, K, Path) -> explore(T1, T2, P, C, X, K, Path, Env) end.

-spec all_goal([goal()]) -> goal().
all_goal(Goals) -> fun(C, X, K, Path) -> all_of(Goals, C, X, K, Path) end.

%% --- the variable level -----------------------------------------------------

%% Make the node T empty under C.
-spec empty(ty:type(), bounds(), achieved(), k(), reason(), env()) -> result().
empty(T, C, X, K, Path, Env = #env{fixed = Fixed}) ->
  case X of
    #{{node, T} := _} -> K(C, X);
    _ ->
      case is_ground(T, Fixed) of
        true ->
          bump(ground),
          case ty_node:is_empty(T) of
            true -> K(C, X);
            false -> {false, Path}
          end;
        false ->
          bump(nodes),
          Lines = dnf_ty_variable:minimize_dnf(ty_node:load(T)),
          Goals = [fun(C1, X1, K1, P1) -> line(L, C1, X1, K1, P1, Env) end || L <- Lines],
          all_of(Goals, C, X#{{node, T} => []}, K, Path)
      end
  end.

%% A type all of whose variables are monomorphic is a constant for tallying:
%% the subtyping engine decides it, treating those variables as atoms exactly
%% as the delta rule of normalize_line does.
-spec is_ground(ty:type(), monomorphic_variables()) -> boolean().
is_ground(T, Fixed) ->
  lists:all(fun(V) -> maps:is_key(V, Fixed) end, sets:to_list(ty_node:all_variables(T))).

%% One DNF line of the variable BDD: alpha_1 & .. & !beta_1 & .. & Leaf <= 0.
%% The NTLV rule singles out the smallest polymorphic variable into one
%% one-sided bound; a line without one is the leaf's problem.
-spec line({[variable()], [variable()], ty_rec:type()}, bounds(), achieved(), k(), reason(), env()) -> result().
line({[], [], Leaf}, C, X, K, Path, Env) ->
  leaf_empty(Leaf, C, X, K, Path, Env);
line({P, N, Leaf}, C, X, K, Path, Env = #env{fixed = Fixed}) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} ->
      U = ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf)),
      bound_upper(V, U, C, X, K, Path, Env);
    {{neg, V}, _} ->
      L = ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf)),
      bound_lower(V, L, C, X, K, Path, Env);
    {{{delta, _}, _}, _} ->
      % only monomorphic variables: they are eliminated (Part 1, Lemma C.3/C.11)
      leaf_empty(Leaf, C, X, K, Path, Env)
  end.

%% alpha <= U, a piece depending on Path. Tightening an existing upper bound
%% obliges the lower bound to fit under the new piece: CL <= U, an empty goal
%% on CL \ U that depends on both pieces' reasons.
-spec bound_upper(variable(), ty:type(), bounds(), achieved(), k(), reason(), env()) -> result().
bound_upper(V, U, C, X, K, Path, Env = #env{empty = Empty}) ->
  bump(bounds),
  case C of
    #{V := {CL, CU, RL, RU}} ->
      case intersect_bound(U, CU, Env) of
        CU -> K(C, X);
        U1 ->
          C1 = C#{V := {CL, U1, RL, maps:merge(RU, Path)}},
          case CL of
            Empty -> K(C1, X);
            _ ->
              bump(consequences),
              empty(ty_node:difference(CL, U), C1, X, K, maps:merge(RL, Path), Env)
          end
      end;
    _ ->
      K(C#{V => {Empty, U, #{}, Path}}, X)
  end.

%% L <= alpha, symmetric: the new lower piece must fit under the upper bound.
-spec bound_lower(variable(), ty:type(), bounds(), achieved(), k(), reason(), env()) -> result().
bound_lower(V, L, C, X, K, Path, Env = #env{any = Any}) ->
  bump(bounds),
  case C of
    #{V := {CL, CU, RL, RU}} ->
      case union_bound(L, CL, Env) of
        CL -> K(C, X);
        L1 ->
          C1 = C#{V := {L1, CU, maps:merge(RL, Path), RU}},
          case CU of
            Any -> K(C1, X);
            _ ->
              bump(consequences),
              empty(ty_node:difference(L, CU), C1, X, K, maps:merge(RU, Path), Env)
          end
      end;
    _ ->
      K(C#{V => {L, Any, Path, #{}}}, X)
  end.

%% --- the leaf level ---------------------------------------------------------

%% A variable-free line is empty iff every component of its leaf is. The
%% basic kinds are decided outright; the structured kinds are searched.
-spec leaf_empty(ty_rec:type(), bounds(), achieved(), k(), reason(), env()) -> result().
leaf_empty(any, _C, _X, _K, Path, _Env) -> {false, Path};
leaf_empty(empty, C, X, K, _Path, _Env) -> K(C, X);
leaf_empty(TyRec, C, X, K, Path, Env) ->
  case basic_empty(TyRec) of
    false -> {false, Path};
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
      all_of(Goals, C, X, K, Path)
  end.

-spec basic_empty(ty_rec:type_record()) -> boolean().
basic_empty(TyRec) ->
  element(1, dnf_ty_predefined:is_empty(ty_rec:pi(TyRec, dnf_ty_predefined), #{}))
    andalso element(1, dnf_ty_atom:is_empty(ty_rec:pi(TyRec, dnf_ty_atom), #{}))
    andalso element(1, dnf_ty_interval:is_empty(ty_rec:pi(TyRec, dnf_ty_interval), #{})).

-spec tuple_goals([{[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}], env()) -> [goal()].
tuple_goals(Lines, Env) ->
  [fun(C, X, K, Path) -> tuple_line(L, C, X, K, Path, Env) end || L <- Lines].

-spec function_goals([{[ty_function:type()], [ty_function:type()], ty_bool:type()}], env()) -> [goal()].
function_goals(Lines, Env) ->
  [fun(C, X, K, Path) -> function_line(L, C, X, K, Path, Env) end || L <- Lines].

-spec map_goals([{[ty_map:type()], [ty_map:type()], ty_bool:type()}], env()) -> [goal()].
map_goals(Lines, Env) ->
  [fun(C, X, K, Path) -> map_line(L, C, X, K, Path, Env) end || L <- Lines].

%% One line of a tuple (or list, bitstring) DNF, as dnf_ty_tuple:normalize_line.
-spec tuple_line({[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}, bounds(), achieved(), k(), reason(), env()) -> result().
tuple_line({[], [], _}, _C, _X, _K, Path, _Env) -> {false, Path}; % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, C, X, K, Path, Env) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, C, X, K, Path, Env);
tuple_line({Pos, Neg, _}, C, X, K, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, C, X, K, Path, Env).

%% One line of a map DNF, as dnf_ty_map:normalize_line: maps are encoded as a
%% pair of a tuple part and a function part, with its own any.
-spec map_line({[ty_map:type()], [ty_map:type()], ty_bool:type()}, bounds(), achieved(), k(), reason(), env()) -> result().
map_line({[], [], _}, _C, _X, _K, Path, _Env) -> {false, Path};
map_line({[], Neg = [_ | _], Leaf}, C, X, K, Path, Env) ->
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  map_line({[ty_map:map(P1, P2)], Neg, Leaf}, C, X, K, Path, Env);
map_line({Pos, Neg, _}, C, X, K, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, C, X, K, Path, Env).

%% S1 x .. x Sn \ (N1 | .. | Nk) <= 0, as dnf_ty_tuple:phi_norm: some Si is
%% empty, or for the first negative tuple N1, for every component i the
%% product with Si \ N1_i is empty without N1. One decision.
-spec phi([ty:type()], [ty_tuple:type()], bounds(), achieved(), k(), reason(), env()) -> result().
phi(BigS, Neg, C, X, K, Path, Env) ->
  Key = {phi, BigS, Neg},
  case X of
    #{Key := _} -> K(C, X);
    _ ->
      bump(phi),
      K1 = fun(C1, X1) -> K(C1, X1#{Key => []}) end,
      Components = [empty_goal(S, Env) || S <- BigS],
      Alternatives = case Neg of
        [] -> Components;
        [Ty | N] -> Components ++ [all_goal(without(BigS, ty_tuple:components(Ty), 1, N, Env))]
      end,
      any_of(Alternatives, C, X, K1, Path)
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
-spec function_line({[ty_function:type()], [ty_function:type()], ty_bool:type()}, bounds(), achieved(), k(), reason(), env()) -> result().
function_line({Pos, Neg, _}, C, X, K, Path, Env) ->
  S = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  NotS = ty_node:negate(S),
  Alternatives =
    [all_goal([empty_goal(ty_node:intersect(ty_function:domain(F), NotS), Env),
               explore_goal(ty_function:domain(F), ty_node:negate(ty_function:codomain(F)), Pos, Env)])
     || F <- Neg],
  any_of(Alternatives, C, X, K, Path).

%% As dnf_ty_function:explore_function_norm: T1 empty, or T2 empty, or the
%% positive arrow S1 -> S2 is split off on both sides. One decision.
-spec explore(ty:type(), ty:type(), [ty_function:type()], bounds(), achieved(), k(), reason(), env()) -> result().
explore(T1, T2, [], C, X, K, Path, Env) ->
  any_of([empty_goal(T1, Env), empty_goal(T2, Env)], C, X, K, Path);
explore(T1, T2, P = [F | Ps], C, X, K, Path, Env) ->
  Key = {explore, T1, T2, P},
  case X of
    #{Key := _} -> K(C, X);
    _ ->
      bump(explore),
      K1 = fun(C1, X1) -> K(C1, X1#{Key => []}) end,
      S1 = ty_function:domain(F),
      S2 = ty_function:codomain(F),
      any_of([empty_goal(T1, Env),
              empty_goal(T2, Env),
              all_goal([explore_goal(T1, ty_node:intersect(T2, S2), Ps, Env),
                        explore_goal(ty_node:difference(T1, S1), T2, Ps, Env)])],
             C, X, K1, Path)
  end.

%% --- bounds -----------------------------------------------------------------

%% Identical nodes need no engine call; the empty and any nodes are units.
-spec union_bound(T, T, env()) -> T when T :: ty:type().
union_bound(A, A, _Env) -> A;
union_bound(Empty, B, #env{empty = Empty}) -> B;
union_bound(A, Empty, #env{empty = Empty}) -> A;
union_bound(A, B, _Env) -> ty_node:union(A, B).

-spec intersect_bound(T, T, env()) -> T when T :: ty:type().
intersect_bound(A, A, _Env) -> A;
intersect_bound(Any, B, #env{any = Any}) -> B;
intersect_bound(A, Any, #env{any = Any}) -> A;
intersect_bound(A, B, _Env) -> ty_node:intersect(A, B).

%% --- counters, metrics only, enabled with PIKE_STATS ------------------------

-spec bump(atom()) -> ok.
bump(Key) ->
  case get(pike_stats) of
    undefined -> ok;
    Counts ->
      put(pike_stats, maps:update_with(Key, fun(N) -> N + 1 end, 1, Counts)),
      ok
  end.

-spec stats_start(env()) -> ok.
stats_start(#env{stats = false}) -> ok;
stats_start(_Env) ->
  put(pike_stats, #{}),
  put(pike_t0, erlang:monotonic_time(microsecond)),
  ok.

-spec stats_stop(env(), non_neg_integer(), boolean()) -> ok.
stats_stop(#env{stats = false}, _N, _Result) -> ok;
stats_stop(_Env, N, Result) ->
  Us = erlang:monotonic_time(microsecond) - get(pike_t0),
  Counts = case get(pike_stats) of undefined -> #{}; Cs -> Cs end,
  erase(pike_stats),
  Get = fun(K) -> maps:get(K, Counts, 0) end,
  io:format(user, "[pike] sat=~p constraints=~p nodes=~p ground=~p bounds=~p "
                  "consequences=~p phi=~p explore=~p backtracks=~p backjumps=~p time=~.1fms~n",
            [Result, N, Get(nodes), Get(ground), Get(bounds), Get(consequences),
             Get(phi), Get(explore), Get(backtracks), Get(backjumps), Us / 1000]),
  ok.
