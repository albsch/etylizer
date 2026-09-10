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
%% alpha, the NTLV rule -- which is merged into C on the spot. A variable's
%% bounds are kept as the pieces that were merged into them; a new piece is
%% checked against every piece on the other side, since
%% (L1 | L2) \ (U1 & U2) = L1 \ U1 | L1 \ U2 | L2 \ U1 | L2 \ U2, and each
%% pair is an empty goal run right away: the consequence that saturation
%% would add later, one piece pair at a time. The search succeeds when the
%% final continuation is reached: every line consumed, every consequence
%% established, C saturated by construction. It fails when every
%% alternative is refuted. The correspondence with a SAT solver:
%%
%%   partial assignment      the bound map C : variable -> {Lower, Upper}
%%   literal                 one one-sided bound from the NTLV rule
%%   decision                an OR of the tuple or function decomposition
%%   theory propagation      the consequence goal of a new piece pair
%%   conflict                a leaf that cannot be made empty under C
%%   conflict analysis       the reason set of a failure: the decisions the
%%                           pieces it read depend on
%%   backjumping             a decision that a failure does not depend on
%%                           does not try its other alternatives
%%   learning                a goal that failed on its own, under the pieces
%%                           it read, fails at once wherever those pieces
%%                           are present
%%   model                   the final continuation reached
%%
%% Reasons. Every piece carries the decisions it depends on (the decisions
%% above the leaf that emitted it), a consequence goal inherits the reasons
%% of the two pieces it relates, a ground leaf that cannot be made empty
%% fails with the reasons of its goal, and a decision whose alternative
%% fails for a reason it is not part of fails with that reason at once: no
%% piece the decision produced was read by the failure, so the same failure
%% exists under every alternative.
%%
%% Learning. Every activation of empty(T) records the pieces it reads, a
%% failure carries the reads that led to it, and a token on the activation's
%% continuation tells a local failure from one of the rest of the search.
%% When an activation fails without its continuation ever having run, T
%% could not be made empty by itself given the pieces it read that existed
%% before it started (its own pieces it would make again): {T, those pieces}
%% is a nogood. Everything a search does depends on C only through the
%% pieces its consequences pair up, so the nogood holds wherever those
%% pieces are present, and a hit fails with exactly their current reasons
%% plus the path of the goal. Pieces are numbered by an epoch on the path to
%% tell an activation's own pieces from the ones it found. The store travels
%% in the search state and comes back in failure results, so what a failed
%% branch learned is known to every later one.
%%
%% Ground goals -- types whose variables are all monomorphic -- are decided
%% by the subtyping engine (ty_node:is_empty, cached in ETS), never walked.
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded in the search
%% state and returned through the continuations: a recursive type met again
%% is assumed empty, and a sub-goal met again on the same path is skipped
%% since its bounds are already in C. Backtracking discards X, the epoch and
%% the reads with the path.
%%
%% Piking searches exactly the tree normalize + saturate materialize:
%% the same minimized lines, the same singled bounds, the same
%% decompositions, with prunings that lose no answer. A goal achieved on the
%% path is not redone (C already lies inside it, the other alternatives only
%% tighten C, and any leaf below a tighter set has a solution that also
%% satisfies C and the pending goals). Skipping an achieved or in-progress
%% goal, or a consequence already implied, only weakens a search, so a
%% failure found with skips holds without them, and a failure under fewer
%% pieces holds under more.

-export([is_satisfiable/2]).

-include("constraints.hrl").

-type input_constraints() :: [{ty:type(), ty:type()}].
%% The decisions a piece, a goal or a failure depends on.
-type reason() :: #{integer() => []}.
%% Pieces are numbered in the order they are made on the path.
-type epoch() :: non_neg_integer().
%% One bound emitted for a variable: the node, the decisions it depends on,
%% and its epoch.
-type piece() :: {ty:type(), reason(), epoch()}.
%% C: the bounds of every variable constrained so far, merged and as pieces:
%% the lower bound is the union of the lower pieces, the upper bound the
%% intersection of the upper pieces.
-type bounds() :: #{variable() => {ty:type(), ty:type(), [piece()], [piece()]}}.
%% X: goals achieved or assumed on the current path. {node, T} is added when
%% empty(T) starts (coinductive hypothesis) and stays; phi and explore keys
%% are added when the sub-goal completes.
-type achieved() :: #{term() => []}.
%% The pieces an activation has read, with their epochs.
-type read() :: {variable(), lower | upper, ty:type()}.
-type reads() :: #{read() => epoch()}.
%% What the search has learned. Nogoods -- the read sets under which
%% empty(T) failed on its own -- are statements about types, valid in every
%% problem with the same monomorphic variables, and live in the engine's
%% caches (ty_node:nogoods/2, learn_nogood/3). Continuation nogoods, per
%% activation: the read sets under which the rest of a conjunction from a
%% given position failed.
-type conts() :: #{integer() => #{term() => [{epoch(), reads()}]}}.
-record(learned, {conts :: conts()}).
-type learned() :: #learned{}.
-record(s, {
  c :: bounds(),
  x :: achieved(),
  epoch :: epoch(),
  reads :: reads(),
  tok :: integer(),      % the activation the search is in
  learned :: learned()
}).
-type s() :: #s{}.
%% A failure names the decisions and the reads it depends on and hands back
%% what was learned; C, X, the epoch and the reads of the path are discarded.
-type result() :: true | {false, reason(), reads(), learned()}.
%% The rest of the search after a goal.
-type k() :: fun((s()) -> result()).
%% A goal runs under the decisions its existence depends on.
-type goal() :: fun((s(), k(), reason()) -> result()).

-define(NOGOODS_PER_NODE, 32). % continuation nogoods per position

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
  %% each input constraint runs under its own tag, so a refutation's reason
  %% names the constraints it used: an unsatisfiable core
  Goals = [fun(S, K, _P) -> empty(ty_node:difference(A, B), S, K, #{{input, I} => []}, Env) end
           || {I, {A, B}} <- lists:enumerate(Constraints)],
  S0 = #s{c = #{}, x = #{}, epoch = 0, reads = #{}, tok = 0,
          learned = #learned{conts = #{}}},
  Result = case all_of(inputs, Goals, S0, fun(_S) -> true end, #{}) of
    true -> true;
    {false, _Reason, _Reads, _Learned} -> false
  end,
  stats_stop(Env, length(Constraints), Result),
  Result.

%% --- combinators ------------------------------------------------------------

%% A conjunction: each goal runs with the rest of the conjunction as its
%% continuation, so a later conjunct that fails backtracks into the choices
%% of the earlier ones -- or past them, if its reason does not involve them.
%% Every conjunction has a structural id. The rest of the conjunction from
%% position I, with what follows it, is the same search whenever it is
%% reached again within the same activation; when it fails, the pieces it
%% read that existed at that point are a continuation nogood, and a later
%% arrival at that position under those pieces fails at once.
-spec all_of(term(), [goal()], s(), k(), reason()) -> result().
all_of(Id, Goals, S, K, Path) -> all_from({Id, 1}, Goals, S, K, Path).

-spec all_from({term(), pos_integer()}, [goal()], s(), k(), reason()) -> result().
all_from(_Pos, [], S, K, _Path) -> K(S);
all_from(Pos = {Id, I}, [G | Gs], S = #s{c = C, epoch = E, reads = Reads0, tok = Tok, learned = Learned}, K, Path) ->
  case known_cont(Tok, Pos, C, Learned) of
    {true, Reads, Reason} ->
      bump(skipped),
      {false, maps:merge(Path, Reason), maps:merge(Reads0, Reads), Learned};
    false ->
      case G(S, fun(S1) -> all_from({Id, I + 1}, Gs, S1, K, Path) end, Path) of
        true -> true;
        {false, R, ReadsF, Learned1} ->
          % the reads are stored as they are with the epoch of the position;
          % the pieces made after it are skipped when the nogood is matched
          {false, R, ReadsF, learn_cont(Tok, Pos, {E, ReadsF}, Learned1)}
      end
  end.

%% A disjunction: a decision. The first alternative under which the whole
%% remaining search succeeds answers the query. An alternative that fails
%% for a reason this decision is not part of fails the decision at once,
%% since the same failure exists under every other alternative; otherwise
%% the next alternative is tried with what the failed one learned, and the
%% reasons and reads of all of them are the reason the decision fails.
-spec any_of([goal()], s(), k(), reason()) -> result().
any_of([], #s{reads = Reads, learned = Learned}, _K, Path) -> {false, Path, Reads, Learned};
any_of(Goals, S, K, Path) ->
  D = erlang:unique_integer([positive]),
  decide(Goals, S, K, Path, D, #{}, S#s.reads).

-spec decide([goal()], s(), k(), reason(), integer(), reason(), reads()) -> result().
decide([], #s{learned = Learned}, _K, _Path, D, Acc, Reads) -> {false, maps:remove(D, Acc), Reads, Learned};
decide([G | Gs], S, K, Path, D, Acc, Reads) ->
  case G(S, K, Path#{D => []}) of
    true -> true;
    {false, R, Reads1, Learned1} ->
      case R of
        #{D := _} ->
          bump(backtracks),
          decide(Gs, S#s{learned = Learned1}, K, Path, D, maps:merge(Acc, R), maps:merge(Reads, Reads1));
        _ ->
          bump(backjumps),
          {false, R, Reads1, Learned1}
      end
  end.

-spec empty_goal(ty:type(), env()) -> goal().
empty_goal(T, Env) -> fun(S, K, Path) -> empty(T, S, K, Path, Env) end.

-spec phi_goal([ty:type()], [ty_tuple:type()], env()) -> goal().
phi_goal(BigS, Neg, Env) -> fun(S, K, Path) -> phi(BigS, Neg, S, K, Path, Env) end.

-spec explore_goal(ty:type(), ty:type(), [ty_function:type()], env()) -> goal().
explore_goal(T1, T2, P, Env) -> fun(S, K, Path) -> explore(T1, T2, P, S, K, Path, Env) end.

-spec all_goal(term(), [goal()]) -> goal().
all_goal(Id, Goals) -> fun(S, K, Path) -> all_of(Id, Goals, S, K, Path) end.

%% --- the variable level -----------------------------------------------------

%% Make the node T empty under C. One activation: it reads into a fresh read
%% set, hands its reads on to the continuation, and if it fails before the
%% continuation ever ran, {T, the pieces it read that predate it} is learned.
-spec empty(ty:type(), s(), k(), reason(), env()) -> result().
empty(Empty, S, K, _Path, #env{empty = Empty}) -> K(S);
empty(Any, #s{reads = Reads, learned = Learned}, _K, Path, #env{any = Any}) -> {false, Path, Reads, Learned};
empty(T, S = #s{c = C, x = X, epoch = E0, reads = Reads0, tok = Tok0, learned = Learned0}, K, Path, Env = #env{fixed = Fixed}) ->
  case X of
    #{{node, T} := _} -> K(S);
    _ ->
      case is_ground(T, Fixed) of
        true ->
          bump(ground),
          case ty_node:is_empty(T) of
            true -> K(S);
            false -> {false, Path, Reads0, Learned0}
          end;
        false ->
          case known_failure(T, Fixed, C) of
            {true, Reads, Reason} ->
              bump(learned),
              {false, maps:merge(Path, Reason), maps:merge(Reads0, Reads), Learned0};
            false ->
              bump(nodes),
              Tok = erlang:unique_integer([positive]),
              K1 = fun(S1 = #s{reads = ReadsIn}) ->
                     Reads1 = case map_size(ReadsIn) of 0 -> Reads0; _ -> maps:merge(Reads0, ReadsIn) end,
                     case K(S1#s{reads = Reads1, tok = Tok0}) of
                       true -> true;
                       {false, R, Rd, Ld} -> {false, R#{Tok => []}, Rd, Ld}
                     end
                   end,
              Prepared = ty_node:cached({pike_lines, T, Fixed}, fun() -> prepare(ty_node:lines(T), Fixed) end),
              Goals = [fun(S1, K2, P1) -> line(L, S1, K2, P1, Env) end || L <- Prepared],
              case all_of({lines, T}, Goals, S#s{x = X#{{node, T} => []}, reads = #{}, tok = Tok}, K1, Path) of
                true -> true;
                {false, R, ReadsIn, Ld} ->
                  Ld1 = forget_conts(Tok, Ld),
                  case R of
                    #{Tok := _} ->
                      {false, maps:remove(Tok, R), ReadsIn, Ld1};
                    _ ->
                      bump(nogoods),
                      Found = maps:filter(fun(_, E) -> E < E0 end, ReadsIn),
                      ty_node:learn_nogood(T, Fixed, Found),
                      {false, R, maps:merge(Reads0, ReadsIn), Ld1}
                  end
              end
          end
      end
  end.

%% The lines of a node, prepared once per node and set of monomorphic
%% variables: a line with a polymorphic variable is its one-sided bound by
%% the NTLV rule -- the smallest such variable singled out against the rest
%% of the line -- and a line without one is its leaf, whose monomorphic
%% variables are eliminated (Part 1, Lemma C.3/C.11). Leaves go first: they
%% are the only lines that can fail on their own.
-type prepared() :: {leaf, ty_rec:type()} | {upper, variable(), ty:type()} | {lower, variable(), ty:type()}.
-spec prepare([{[variable()], [variable()], ty_rec:type()}], monomorphic_variables()) -> [prepared()].
prepare(Lines, Fixed) ->
  Prepared = [prepare_line(L, Fixed) || L <- Lines],
  {Leaves, Bounds} = lists:partition(fun({leaf, _}) -> true; (_) -> false end, Prepared),
  Leaves ++ Bounds.

-spec prepare_line({[variable()], [variable()], ty_rec:type()}, monomorphic_variables()) -> prepared().
prepare_line({[], [], Leaf}, _Fixed) -> {leaf, Leaf};
prepare_line({P, N, Leaf}, Fixed) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} -> {upper, V, ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf))};
    {{neg, V}, _} -> {lower, V, ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf))};
    {{{delta, _}, _}, _} -> {leaf, Leaf}
  end.

%% A type all of whose variables are monomorphic is a constant for tallying:
%% the subtyping engine decides it, treating those variables as atoms exactly
%% as the delta rule of normalize_line does.
-spec is_ground(ty:type(), monomorphic_variables()) -> boolean().
is_ground(T, Fixed) when map_size(Fixed) =:= 0 ->
  sets:is_empty(ty_node:all_variables(T));
is_ground(T, Fixed) ->
  lists:all(fun(V) -> maps:is_key(V, Fixed) end, sets:to_list(ty_node:all_variables(T))).

%% One prepared line: alpha_1 & .. & !beta_1 & .. & Leaf <= 0 is a bound on
%% its smallest polymorphic variable, or its leaf's problem.
-spec line(prepared(), s(), k(), reason(), env()) -> result().
line({leaf, Leaf}, S, K, Path, Env) -> leaf_empty(Leaf, S, K, Path, Env);
line({upper, V, U}, S, K, Path, Env) -> bound_upper(V, U, S, K, Path, Env);
line({lower, V, L}, S, K, Path, Env) -> bound_lower(V, L, S, K, Path, Env).

%% alpha <= U, a piece depending on Path. A piece the current upper bound
%% already implies changes nothing. Otherwise every lower piece must fit
%% under the new one: one consequence per pair, each reading the lower piece.
-spec bound_upper(variable(), ty:type(), s(), k(), reason(), env()) -> result().
bound_upper(V, U, S = #s{c = C, epoch = E}, K, Path, Env = #env{empty = Empty, any = Any}) ->
  bump(bounds),
  case C of
    #{V := {CL, CU, Ls, Us}} ->
      case intersect_bound(U, CU, Env) of
        CU -> K(S);
        U1 ->
          S1 = S#s{c = C#{V := {CL, U1, Ls, [{U, Path, E} | Us]}}, epoch = E + 1},
          consequences({upper, V, U}, [{ty_node:difference(L, U), maps:merge(RL, Path), {V, lower, L}, EL}
                                        || {L, RL, EL} <- Ls], S1, K, Env)
      end;
    _ ->
      K(S#s{c = C#{V => {Empty, U, [], [{U, Path, E}]}}, epoch = E + 1})
  end.

%% L <= alpha, symmetric: the new lower piece must fit under every upper piece.
-spec bound_lower(variable(), ty:type(), s(), k(), reason(), env()) -> result().
bound_lower(V, L, S = #s{c = C, epoch = E}, K, Path, Env = #env{empty = Empty, any = Any}) ->
  bump(bounds),
  case C of
    #{V := {CL, CU, Ls, Us}} ->
      case union_bound(L, CL, Env) of
        CL -> K(S);
        L1 ->
          S1 = S#s{c = C#{V := {L1, CU, [{L, Path, E} | Ls], Us}}, epoch = E + 1},
          consequences({lower, V, L}, [{ty_node:difference(L, U), maps:merge(RU, Path), {V, upper, U}, EU}
                                        || {U, RU, EU} <- Us], S1, K, Env)
      end;
    _ ->
      K(S#s{c = C#{V => {L, Any, [{L, Path, E}], []}}, epoch = E + 1})
  end.

%% The consequences of a new piece: for every piece on the other side, the
%% pair must satisfy lower <= upper. Each is an empty goal under the two
%% pieces' reasons, and reads the piece it was paired with.
-spec consequences(term(), [{ty:type(), reason(), read(), epoch()}], s(), k(), env()) -> result().
consequences(Id, Pairs, S, K, Env = #env{empty = Empty}) ->
  % a pair whose difference is the empty node holds by itself: no goal, no read
  Goals = [fun(S0 = #s{reads = Reads}, K0, _P) ->
             bump(consequences),
             empty(T, S0#s{reads = Reads#{Read => Epoch}}, K0, Path, Env)
           end || {T, Path, Read, Epoch} <- Pairs, T =/= Empty],
  case Goals of
    [] -> K(S);
    _ -> all_of(Id, Goals, S, K, #{})
  end.

%% --- learning ---------------------------------------------------------------

-spec learn_cont(integer(), {term(), pos_integer()}, {epoch(), reads()}, learned()) -> learned().
learn_cont(Tok, Pos, Entry, Learned = #learned{conts = Conts}) ->
  Mine = maps:get(Tok, Conts, #{}),
  Known = maps:get(Pos, Mine, []),
  case lists:member(Entry, Known) of
    true -> Learned;
    false -> Learned#learned{conts = Conts#{Tok => Mine#{Pos => lists:sublist([Entry | Known], ?NOGOODS_PER_NODE)}}}
  end.

%% An activation's continuation nogoods die with it.
-spec forget_conts(integer(), learned()) -> learned().
forget_conts(Tok, Learned = #learned{conts = Conts}) ->
  Learned#learned{conts = maps:remove(Tok, Conts)}.

-spec known_cont(integer(), {term(), pos_integer()}, bounds(), learned()) -> false | {true, reads(), reason()}.
known_cont(Tok, Pos, C, #learned{conts = Conts}) ->
  case Conts of
    #{Tok := #{Pos := Known}} -> match_conts(Known, C);
    _ -> false
  end.

-spec match_conts([{epoch(), reads()}], bounds()) -> false | {true, reads(), reason()}.
match_conts([], _C) -> false;
match_conts([{E, Reads} | Rest], C) ->
  case present_before(maps:next(maps:iterator(Reads)), E, C, []) of
    {true, Current, Reason} -> {true, Current, Reason};
    false -> match_conts(Rest, C)
  end.

%% present/4 over the reads of pieces older than E, the rest skipped.
-spec present_before(none | {read(), epoch(), maps:iterator()}, epoch(), bounds(), [{read(), piece()}]) -> false | {true, reads(), reason()}.
present_before(none, _E, C, Found) -> present([], C, Found);
present_before({_Read, Ep, Next}, E, C, Found) when Ep >= E ->
  present_before(maps:next(Next), E, C, Found);
present_before({Read = {V, Side, Node}, _Ep, Next}, E, C, Found) ->
  case C of
    #{V := {_, _, Ls, Us}} ->
      case lists:keyfind(Node, 1, case Side of lower -> Ls; upper -> Us end) of
        Piece = {Node, _, _} -> present_before(maps:next(Next), E, C, [{Read, Piece} | Found]);
        false -> false
      end;
    _ -> false
  end.

%% A nogood applies when every piece it read is present. Its reads come back
%% with the pieces' current epochs, and its reason is the pieces' current
%% reasons.
-spec known_failure(ty:type(), monomorphic_variables(), bounds()) -> false | {true, reads(), reason()}.
known_failure(T, Fixed, C) ->
  case ty_node:nogoods(T, Fixed) of
    [] -> false;
    Known -> match_nogoods(Known, C)
  end.

-spec match_nogoods([reads()], bounds()) -> false | {true, reads(), reason()}.
match_nogoods([], _C) -> false;
match_nogoods([Reads | Rest], C) ->
  case present(maps:keys(Reads), C, []) of
    {true, Current, Reason} -> {true, Current, Reason};
    false -> match_nogoods(Rest, C)
  end.

%% The reads and reasons of a match are built only once every piece is found.
-spec present([read()], bounds(), [{read(), piece()}]) -> false | {true, reads(), reason()}.
present([], _C, Found) ->
  {true,
   maps:from_list([{Read, E} || {Read, {_, _, E}} <- Found]),
   lists:foldl(fun({_, {_, R, _}}, Acc) -> maps:merge(Acc, R) end, #{}, Found)};
present([Read = {V, Side, Node} | Rest], C, Found) ->
  case C of
    #{V := {_, _, Ls, Us}} ->
      Pieces = case Side of lower -> Ls; upper -> Us end,
      case lists:keyfind(Node, 1, Pieces) of
        Piece = {Node, _, _} -> present(Rest, C, [{Read, Piece} | Found]);
        false -> false
      end;
    _ -> false
  end.

%% --- the leaf level ---------------------------------------------------------

%% A variable-free line is empty iff every component of its leaf is. The
%% basic kinds are decided outright; the structured kinds are searched.
-spec leaf_empty(ty_rec:type(), s(), k(), reason(), env()) -> result().
leaf_empty(any, #s{reads = Reads, learned = Learned}, _K, Path, _Env) -> {false, Path, Reads, Learned};
leaf_empty(empty, S, K, _Path, _Env) -> K(S);
leaf_empty(TyRec, S = #s{reads = Reads, learned = Learned}, K, Path, Env) ->
  case basic_empty(TyRec) of
    false -> {false, Path, Reads, Learned};
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
      all_of({leaf, TyRec}, Goals, S, K, Path)
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
tuple_line({[], [], _}, #s{reads = Reads, learned = Learned}, _K, Path, _Env) ->
  {false, Path, Reads, Learned}; % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, S, K, Path, Env) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, S, K, Path, Env);
tuple_line({Pos, Neg, _}, S, K, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, S, K, Path, Env).

%% One line of a map DNF, as dnf_ty_map:normalize_line: maps are encoded as a
%% pair of a tuple part and a function part, with its own any.
-spec map_line({[ty_map:type()], [ty_map:type()], ty_bool:type()}, s(), k(), reason(), env()) -> result().
map_line({[], [], _}, #s{reads = Reads, learned = Learned}, _K, Path, _Env) -> {false, Path, Reads, Learned};
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
      bump(phi),
      K1 = fun(S1 = #s{x = X1}) -> K(S1#s{x = X1#{Key => []}}) end,
      case lists:any(fun(Si) -> maps:is_key({node, Si}, X) end, BigS) of
        true -> K1(S);
        false ->
          Components = [empty_goal(Si, Env) || Si <- BigS],
          Alternatives = case Neg of
            [] -> Components;
            [Ty | N] -> Components ++ [all_goal({Key, split}, without(BigS, ty_tuple:components(Ty), 1, N, Env))]
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
%% which needs T1 inside the union of the domains and explore to hold.
%% Which negative arrow is one decision.
-spec function_line({[ty_function:type()], [ty_function:type()], ty_bool:type()}, s(), k(), reason(), env()) -> result().
function_line({Pos, Neg, _}, S, K, Path, Env) ->
  Dom = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  NotDom = ty_node:negate(Dom),
  Alternatives =
    [all_goal({function_line, Pos, F},
              [empty_goal(ty_node:intersect(ty_function:domain(F), NotDom), Env),
               explore_goal(ty_function:domain(F), ty_node:negate(ty_function:codomain(F)), Pos, Env)])
     || F <- Neg],
  any_of(Alternatives, S, K, Path).

%% As dnf_ty_function:explore_function_norm: T1 empty, or T2 empty, or the
%% positive arrow S1 -> S2 is split off on both sides. One decision, unless
%% T1 or T2 is already empty on this path.
-spec explore(ty:type(), ty:type(), [ty_function:type()], s(), k(), reason(), env()) -> result().
explore(T1, T2, P, S = #s{x = X}, K, Path, Env) ->
  Key = {explore, T1, T2, P},
  case X of
    #{Key := _} -> K(S);
    _ ->
      bump(explore),
      K1 = fun(S1 = #s{x = X1}) -> K(S1#s{x = X1#{Key => []}}) end,
      case maps:is_key({node, T1}, X) orelse maps:is_key({node, T2}, X) of
        true -> K1(S);
        false ->
          Split = case P of
            [] -> [];
            [F | Ps] ->
              S1 = ty_function:domain(F),
              S2 = ty_function:codomain(F),
              [all_goal({Key, split},
                        [explore_goal(T1, ty_node:intersect(T2, S2), Ps, Env),
                         explore_goal(ty_node:difference(T1, S1), T2, Ps, Env)])]
          end,
          any_of([empty_goal(T1, Env), empty_goal(T2, Env) | Split], S, K1, Path)
      end
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
                  "consequences=~p phi=~p explore=~p backtracks=~p backjumps=~p "
                  "nogoods=~p learned=~p skipped=~p time=~.1fms~n",
            [Result, N, Get(nodes), Get(ground), Get(bounds), Get(consequences),
             Get(phi), Get(explore), Get(backtracks), Get(backjumps),
             Get(nogoods), Get(learned), Get(skipped), Us / 1000]),
  ok.
