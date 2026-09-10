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
%% negative arrow refuting the line) is a choice point that backtracks, and a
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
%%   clause / decision       an OR of the tuple or function decomposition
%%   theory propagation      the consequence goal of a tightened pair
%%   conflict                a leaf that cannot be made empty under C
%%   model                   the final continuation reached
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
%% decompositions in the same order, with two prunings that lose no answer.
%% A goal achieved on the path is not redone (C already lies inside it, the
%% other alternatives only tighten C, and any leaf below a tighter set has a
%% solution that also satisfies C and the pending goals). And the
%% consequence of a tightened pair is its incremental part: every pair
%% (lower piece, upper piece) is covered when the later of the two arrives.

-export([is_satisfiable/2]).

-include("constraints.hrl").

-type input_constraints() :: [{ty:type(), ty:type()}].
%% C: the current bounds of every variable constrained so far.
-type bounds() :: #{variable() => {ty:type(), ty:type()}}.
%% X: goals achieved or assumed on the current path. {node, T} is added when
%% empty(T) starts (coinductive hypothesis) and stays; phi and explore keys
%% are added when the sub-goal completes.
-type achieved() :: #{term() => []}.
%% The rest of the search after a goal: takes the bounds and achieved set
%% the goal produced, returns whether the whole remaining search succeeds.
-type k() :: fun((bounds(), achieved()) -> boolean()).
-type goal() :: fun((bounds(), achieved(), k()) -> boolean()).

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
  Result = all_of(Goals, #{}, #{}, fun(_C, _X) -> true end),
  stats_stop(Env, length(Constraints), Result),
  Result.

%% --- combinators ------------------------------------------------------------

%% A conjunction: each goal runs with the rest of the conjunction as its
%% continuation, so a later conjunct that fails backtracks into the choices
%% of the earlier ones.
-spec all_of([goal()], bounds(), achieved(), k()) -> boolean().
all_of([], C, X, K) -> K(C, X);
all_of([G | Gs], C, X, K) ->
  G(C, X, fun(C1, X1) -> all_of(Gs, C1, X1, K) end).

%% A disjunction: a choice point. The first alternative under which the
%% whole remaining search succeeds answers the query.
-spec any_of([goal()], bounds(), achieved(), k()) -> boolean().
any_of([], _C, _X, _K) -> false;
any_of([G | Gs], C, X, K) ->
  G(C, X, K) orelse (bump(backtracks) andalso any_of(Gs, C, X, K)).

-spec empty_goal(ty:type(), env()) -> goal().
empty_goal(T, Env) -> fun(C, X, K) -> empty(T, C, X, K, Env) end.

-spec phi_goal([ty:type()], [ty_tuple:type()], env()) -> goal().
phi_goal(BigS, Neg, Env) -> fun(C, X, K) -> phi(BigS, Neg, C, X, K, Env) end.

-spec explore_goal(ty:type(), ty:type(), [ty_function:type()], env()) -> goal().
explore_goal(T1, T2, P, Env) -> fun(C, X, K) -> explore(T1, T2, P, C, X, K, Env) end.

%% --- the variable level -----------------------------------------------------

%% Make the node T empty under C.
-spec empty(ty:type(), bounds(), achieved(), k(), env()) -> boolean().
empty(T, C, X, K, Env = #env{fixed = Fixed}) ->
  case X of
    #{{node, T} := _} -> K(C, X);
    _ ->
      case is_ground(T, Fixed) of
        true ->
          bump(ground),
          case ty_node:is_empty(T) of
            true -> K(C, X);
            false -> false
          end;
        false ->
          bump(nodes),
          Lines = dnf_ty_variable:minimize_dnf(ty_node:load(T)),
          Goals = [fun(C1, X1, K1) -> line(L, C1, X1, K1, Env) end || L <- Lines],
          all_of(Goals, C, X#{{node, T} => []}, K)
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
-spec line({[variable()], [variable()], ty_rec:type()}, bounds(), achieved(), k(), env()) -> boolean().
line({[], [], Leaf}, C, X, K, Env) ->
  leaf_empty(Leaf, C, X, K, Env);
line({P, N, Leaf}, C, X, K, Env = #env{fixed = Fixed}) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} ->
      U = ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf)),
      bound_upper(V, U, C, X, K, Env);
    {{neg, V}, _} ->
      L = ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf)),
      bound_lower(V, L, C, X, K, Env);
    {{{delta, _}, _}, _} ->
      % only monomorphic variables: they are eliminated (Part 1, Lemma C.3/C.11)
      leaf_empty(Leaf, C, X, K, Env)
  end.

%% alpha <= U. Tightening an existing upper bound obliges the lower bound to
%% fit under the new piece: CL <= U, an empty goal on CL \ U.
-spec bound_upper(variable(), ty:type(), bounds(), achieved(), k(), env()) -> boolean().
bound_upper(V, U, C, X, K, Env = #env{empty = Empty}) ->
  bump(bounds),
  case C of
    #{V := {CL, CU}} ->
      case intersect_bound(U, CU, Env) of
        CU -> K(C, X);
        U1 ->
          C1 = C#{V := {CL, U1}},
          case CL of
            Empty -> K(C1, X);
            _ ->
              bump(consequences),
              empty(ty_node:difference(CL, U), C1, X, K, Env)
          end
      end;
    _ ->
      K(C#{V => {Empty, U}}, X)
  end.

%% L <= alpha, symmetric: the new lower piece must fit under the upper bound.
-spec bound_lower(variable(), ty:type(), bounds(), achieved(), k(), env()) -> boolean().
bound_lower(V, L, C, X, K, Env = #env{any = Any}) ->
  bump(bounds),
  case C of
    #{V := {CL, CU}} ->
      case union_bound(L, CL, Env) of
        CL -> K(C, X);
        L1 ->
          C1 = C#{V := {L1, CU}},
          case CU of
            Any -> K(C1, X);
            _ ->
              bump(consequences),
              empty(ty_node:difference(L, CU), C1, X, K, Env)
          end
      end;
    _ ->
      K(C#{V => {L, Any}}, X)
  end.

%% --- the leaf level ---------------------------------------------------------

%% A variable-free line is empty iff every component of its leaf is. The
%% basic kinds are decided outright; the structured kinds are searched.
-spec leaf_empty(ty_rec:type(), bounds(), achieved(), k(), env()) -> boolean().
leaf_empty(any, _C, _X, _K, _Env) -> false;
leaf_empty(empty, C, X, K, _Env) -> K(C, X);
leaf_empty(TyRec, C, X, K, Env) ->
  case basic_empty(TyRec) of
    false -> false;
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
      all_of(Goals, C, X, K)
  end.

-spec basic_empty(ty_rec:type_record()) -> boolean().
basic_empty(TyRec) ->
  element(1, dnf_ty_predefined:is_empty(ty_rec:pi(TyRec, dnf_ty_predefined), #{}))
    andalso element(1, dnf_ty_atom:is_empty(ty_rec:pi(TyRec, dnf_ty_atom), #{}))
    andalso element(1, dnf_ty_interval:is_empty(ty_rec:pi(TyRec, dnf_ty_interval), #{})).

-spec tuple_goals([{[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}], env()) -> [goal()].
tuple_goals(Lines, Env) ->
  [fun(C, X, K) -> tuple_line(L, C, X, K, Env) end || L <- Lines].

-spec function_goals([{[ty_function:type()], [ty_function:type()], ty_bool:type()}], env()) -> [goal()].
function_goals(Lines, Env) ->
  [fun(C, X, K) -> function_line(L, C, X, K, Env) end || L <- Lines].

-spec map_goals([{[ty_map:type()], [ty_map:type()], ty_bool:type()}], env()) -> [goal()].
map_goals(Lines, Env) ->
  [fun(C, X, K) -> map_line(L, C, X, K, Env) end || L <- Lines].

%% One line of a tuple (or list, bitstring) DNF, as dnf_ty_tuple:normalize_line.
-spec tuple_line({[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}, bounds(), achieved(), k(), env()) -> boolean().
tuple_line({[], [], _}, _C, _X, _K, _Env) -> false; % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, C, X, K, Env) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, C, X, K, Env);
tuple_line({Pos, Neg, _}, C, X, K, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, C, X, K, Env).

%% One line of a map DNF, as dnf_ty_map:normalize_line: maps are encoded as a
%% pair of a tuple part and a function part, with its own any.
-spec map_line({[ty_map:type()], [ty_map:type()], ty_bool:type()}, bounds(), achieved(), k(), env()) -> boolean().
map_line({[], [], _}, _C, _X, _K, _Env) -> false;
map_line({[], Neg = [_ | _], Leaf}, C, X, K, Env) ->
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  map_line({[ty_map:map(P1, P2)], Neg, Leaf}, C, X, K, Env);
map_line({Pos, Neg, _}, C, X, K, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, C, X, K, Env).

%% S1 x .. x Sn \ (N1 | .. | Nk) <= 0, as dnf_ty_tuple:phi_norm: some Si is
%% empty, or for the first negative tuple N1, for every component i the
%% product with Si \ N1_i is empty without N1.
-spec phi([ty:type()], [ty_tuple:type()], bounds(), achieved(), k(), env()) -> boolean().
phi(BigS, Neg, C, X, K, Env) ->
  Key = {phi, BigS, Neg},
  case X of
    #{Key := _} -> K(C, X);
    _ ->
      bump(phi),
      K1 = fun(C1, X1) -> K(C1, X1#{Key => []}) end,
      Components = [empty_goal(S, Env) || S <- BigS],
      case Neg of
        [] -> any_of(Components, C, X, K1);
        [Ty | N] ->
          any_of(Components, C, X, K1)
            orelse all_of(without(BigS, ty_tuple:components(Ty), 1, N, Env), C, X, K1)
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
-spec function_line({[ty_function:type()], [ty_function:type()], ty_bool:type()}, bounds(), achieved(), k(), env()) -> boolean().
function_line({Pos, Neg, _}, C, X, K, Env) ->
  S = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  function_cont(S, Pos, Neg, C, X, K, Env).

-spec function_cont(ty:type(), [ty_function:type()], [ty_function:type()], bounds(), achieved(), k(), env()) -> boolean().
function_cont(_S, _P, [], _C, _X, _K, _Env) -> false; % no negative arrow: never empty
function_cont(S, P, [F | N], C, X, K, Env) ->
  T1 = ty_function:domain(F),
  T2 = ty_function:codomain(F),
  all_of([empty_goal(ty_node:intersect(T1, ty_node:negate(S)), Env),
          explore_goal(T1, ty_node:negate(T2), P, Env)], C, X, K)
    orelse (bump(backtracks) andalso function_cont(S, P, N, C, X, K, Env)).

%% As dnf_ty_function:explore_function_norm: T1 empty, or T2 empty, or the
%% positive arrow S1 -> S2 is split off on both sides.
-spec explore(ty:type(), ty:type(), [ty_function:type()], bounds(), achieved(), k(), env()) -> boolean().
explore(T1, T2, [], C, X, K, Env) ->
  any_of([empty_goal(T1, Env), empty_goal(T2, Env)], C, X, K);
explore(T1, T2, P = [F | Ps], C, X, K, Env) ->
  Key = {explore, T1, T2, P},
  case X of
    #{Key := _} -> K(C, X);
    _ ->
      bump(explore),
      K1 = fun(C1, X1) -> K(C1, X1#{Key => []}) end,
      S1 = ty_function:domain(F),
      S2 = ty_function:codomain(F),
      any_of([empty_goal(T1, Env), empty_goal(T2, Env)], C, X, K1)
        orelse all_of([explore_goal(T1, ty_node:intersect(T2, S2), Ps, Env),
                       explore_goal(ty_node:difference(T1, S1), T2, Ps, Env)], C, X, K1)
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

-spec bump(atom()) -> true.
bump(Key) ->
  case get(pike_stats) of
    undefined -> true;
    Counts ->
      put(pike_stats, maps:update_with(Key, fun(N) -> N + 1 end, 1, Counts)),
      true
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
                  "consequences=~p phi=~p explore=~p backtracks=~p time=~.1fms~n",
            [Result, N, Get(nodes), Get(ground), Get(bounds), Get(consequences),
             Get(phi), Get(explore), Get(backtracks), Us / 1000]),
  ok.
