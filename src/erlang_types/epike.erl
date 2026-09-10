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
%% line) is a decision that pushes its remaining alternatives onto the
%% trail and backtracks, and a leaf emits ONE one-sided bound -- alpha <=
%% single(...) or single(...) <= alpha, the NTLV rule -- which is merged
%% into C on the spot. A variable's bounds are kept as the pieces that were
%% merged into them; a new piece is checked against every piece on the
%% other side, since
%% (L1 | L2) \ (U1 & U2) = L1 \ U1 | L1 \ U2 | L2 \ U1 | L2 \ U2, and each
%% pair is an empty goal run right away: the consequence that saturation
%% would add later, one piece pair at a time. The search succeeds when K is
%% exhausted: every line consumed, every consequence established, C
%% saturated by construction. It fails when the trail is: every alternative
%% refuted. The correspondence with a SAT solver:
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
%%   model                   K exhausted
%%
%% The engine. Goals are data, and the search is three mutually
%% tail-recursive functions, so it runs in constant Erlang stack however
%% deep the path:
%%
%%   goal/6   runs a goal under the current state and path
%%   ret/4    the goal succeeded: the next frame of K runs -- the remaining
%%            conjuncts of an enclosing conjunction, the exit of an
%%            enclosing activation, the key of an enclosing phi or explore
%%            goal to add to X
%%   fail/5   the goal failed: the trail is unwound, every handler seeing
%%            the failure in turn -- the continuation nogood of every
%%            conjunct on the path, the tag of every activation whose
%%            continuation ran, the nogood of every activation that failed
%%            on its own -- until a decision the failure depends on has an
%%            alternative left
%%
%% A frame of K is what a continuation closes over, and the trail is the
%% call stack a failure returns through in continuation-passing style: it
%% grows with every conjunct run and shrinks only when a failure unwinds
%% it. A decision keeps the state and K it was made under, so its next
%% alternative starts from them; K is a list, shared by every alternative.
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
%% failure carries the reads that led to it, and a tag on the trail, pushed
%% when the activation exits, tells a local failure from one of the rest of
%% the search. When an activation fails without ever having exited, T
%% could not be made empty by itself given the pieces it read that existed
%% before it started (its own pieces it would make again): {T, those pieces}
%% is a nogood. Everything a search does depends on C only through the
%% pieces its consequences pair up, so the nogood holds wherever those
%% pieces are present, and a hit fails with exactly their current reasons
%% plus the path of the goal. Pieces are numbered by an epoch on the path to
%% tell an activation's own pieces from the ones it found. The store travels
%% in the search state and comes back in failures, so what a failed branch
%% learned is known to every later one.
%%
%% Ground goals -- types whose variables are all monomorphic -- are decided
%% by the subtyping engine (ty_node:is_empty, cached in ETS), never walked.
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded in the search
%% state along K: a recursive type met again is assumed empty, and a
%% sub-goal met again on the same path is skipped since its bounds are
%% already in C. Backtracking discards X, the epoch and the reads with the
%% path.
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

%% A goal. The lines of a node and the components of a leaf are goals as
%% they are prepared.
-type goal() :: {input, pos_integer(), ty:type(), ty:type()}   % the input constraint A <= B
              | {empty, ty:type()}                             % make the node empty
              | {consequence, ty:type(), reason(), read(), epoch()} % a piece pair, reading one of them
              | {all, term(), [goal()]}                        % a conjunction
              | {phi, [ty:type()], [ty_tuple:type()]}
              | {explore, ty:type(), ty:type(), [ty_function:type()]}
              | prepared() | component().
%% K, the rest of the search after a goal, innermost frame first.
-type frame() :: {conj, term(), pos_integer(), [goal(), ...], reason()} % a conjunction from a position on
               | {exit, reads(), integer(), integer()}   % leave an activation: its reads, the enclosing token, its own
               | {achieve, term()}.                      % a phi or explore goal completed
-type k() :: [frame()].
%% The trail: what a failure meets on its way back, innermost first.
-type handler() :: {cont, integer(), {term(), pos_integer()}, epoch()} % a conjunct ran: learn a continuation nogood
                 | {decide, [goal()], s(), k(), reason(), integer(), reason(), reads()} % a decision: alternatives left, its state
                 | {tag, integer()}                                   % an activation exited: its continuation failed
                 | {activation, ty:type(), integer(), epoch(), reads()}. % an activation started: learn its nogood
-type trail() :: [handler()].

-define(NOGOODS_PER_NODE, 32). % continuation nogoods per position

-record(env, {
  fixed :: monomorphic_variables()
}).
-type env() :: #env{}.

-spec is_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable(Constraints, Fixed) ->
  Env = #env{fixed = Fixed},
  %% each input constraint runs under its own tag, so a refutation's reason
  %% names the constraints it used: an unsatisfiable core
  Goals = [{input, I, A, B} || {I, {A, B}} <- lists:enumerate(Constraints)],
  S0 = #s{c = #{}, x = #{}, epoch = 0, reads = #{}, tok = 0,
          learned = #learned{conts = #{}}},
  all_of(inputs, Goals, S0, [], [], #{}, Env).

%% --- the engine -------------------------------------------------------------

%% Run a goal under the decisions its existence depends on.
-spec goal(goal(), s(), k(), trail(), reason(), env()) -> boolean().
goal({input, I, A, B}, S, K, Tr, _Path, Env) ->
  empty(ty_node:difference(A, B), S, K, Tr, #{{input, I} => []}, Env);
goal({empty, T}, S, K, Tr, Path, Env) ->
  empty(T, S, K, Tr, Path, Env);
goal({consequence, T, Path, Read, Epoch}, S = #s{reads = Reads}, K, Tr, _Path, Env) ->
  empty(T, S#s{reads = Reads#{Read => Epoch}}, K, Tr, Path, Env);
goal({all, Id, Goals}, S, K, Tr, Path, Env) ->
  all_of(Id, Goals, S, K, Tr, Path, Env);
goal({phi, BigS, Neg}, S, K, Tr, Path, Env) ->
  phi(BigS, Neg, S, K, Tr, Path, Env);
goal({explore, T1, T2, P}, S, K, Tr, Path, Env) ->
  explore(T1, T2, P, S, K, Tr, Path, Env);
goal(dead, S, _K, Tr, Path, Env) ->
  fail(Path, S, Tr, Env);
goal({leaf, Id, Components}, S, K, Tr, Path, Env) ->
  all_of({leaf, Id}, Components, S, K, Tr, Path, Env);
goal({upper, V, U}, S, K, Tr, Path, Env) ->
  bound_upper(V, U, S, K, Tr, Path, Env);
goal({lower, V, L}, S, K, Tr, Path, Env) ->
  bound_lower(V, L, S, K, Tr, Path, Env);
goal({tuple, L}, S, K, Tr, Path, Env) ->
  tuple_line(L, S, K, Tr, Path, Env);
goal({function, L}, S, K, Tr, Path, Env) ->
  function_line(L, S, K, Tr, Path, Env);
goal({map, L}, S, K, Tr, Path, Env) ->
  map_line(L, S, K, Tr, Path, Env).

%% The goal succeeded: the next frame of K runs, and the search succeeds
%% when there is none.
-spec ret(s(), k(), trail(), env()) -> boolean().
ret(_S, [], _Tr, _Env) -> true;
ret(S, [{conj, Id, I, Goals, Path} | K], Tr, Env) ->
  all_from({Id, I}, Goals, S, K, Tr, Path, Env);
ret(S = #s{reads = ReadsIn}, [{exit, Reads0, Tok0, Tok} | K], Tr, Env) ->
  % the activation hands its reads on; from here on a failure is one of
  % the rest of the search, which the tag tells its activation
  Reads1 = case map_size(ReadsIn) of 0 -> Reads0; _ -> maps:merge(Reads0, ReadsIn) end,
  ret(S#s{reads = Reads1, tok = Tok0}, K, [{tag, Tok} | Tr], Env);
ret(S = #s{x = X}, [{achieve, Key} | K], Tr, Env) ->
  ret(S#s{x = X#{Key => []}}, K, Tr, Env).

%% A goal fails at once under the decisions of its path, with the reads and
%% what was learned of the state it failed in.
-spec fail(reason(), s(), trail(), env()) -> boolean().
fail(Path, #s{reads = Reads, learned = Learned}, Tr, Env) -> fail(Path, Reads, Learned, Tr, Env).

%% The search failed for reason R, having read Reads: every handler on the
%% trail sees the failure in turn, until a decision it depends on has an
%% alternative left, and the search fails when there is none.
-spec fail(reason(), reads(), learned(), trail(), env()) -> boolean().
fail(_R, _Reads, _Learned, [], _Env) -> false;
fail(R, Reads, Learned, [{cont, Tok, Pos, E} | Tr], Env) ->
  % the reads are stored as they are with the epoch of the position;
  % the pieces made after it are skipped when the nogood is matched
  fail(R, Reads, learn_cont(Tok, Pos, {E, Reads}, Learned), Tr, Env);
fail(R, Reads, Learned, [{decide, Goals, S, K, Path, D, Acc, ReadsAcc} | Tr], Env) ->
  case R of
    #{D := _} ->
      decide(Goals, S#s{learned = Learned}, K, Tr, Path, D, maps:merge(Acc, R), maps:merge(ReadsAcc, Reads), Env);
    _ ->
      fail(R, Reads, Learned, Tr, Env)
  end;
fail(R, Reads, Learned, [{tag, Tok} | Tr], Env) ->
  fail(R#{Tok => []}, Reads, Learned, Tr, Env);
fail(R, ReadsIn, Learned, [{activation, T, Tok, E0, Reads0} | Tr], Env = #env{fixed = Fixed}) ->
  Learned1 = forget_conts(Tok, Learned),
  case R of
    #{Tok := _} ->
      fail(maps:remove(Tok, R), ReadsIn, Learned1, Tr, Env);
    _ ->
      Found = maps:filter(fun(_, E) -> E < E0 end, ReadsIn),
      ty_node:learn_nogood(T, Fixed, Found),
      fail(R, maps:merge(Reads0, ReadsIn), Learned1, Tr, Env)
  end.

%% A conjunction: each goal runs with the rest of the conjunction on K, so a
%% later conjunct that fails backtracks into the choices of the earlier
%% ones -- or past them, if its reason does not involve them. Every
%% conjunction has a structural id. The rest of the conjunction from
%% position I, with what follows it, is the same search whenever it is
%% reached again within the same activation; when it fails, the pieces it
%% read that existed at that point are a continuation nogood, and a later
%% arrival at that position under those pieces fails at once.
-spec all_of(term(), [goal()], s(), k(), trail(), reason(), env()) -> boolean().
all_of(Id, Goals, S, K, Tr, Path, Env) -> all_from({Id, 1}, Goals, S, K, Tr, Path, Env).

-spec all_from({term(), pos_integer()}, [goal()], s(), k(), trail(), reason(), env()) -> boolean().
all_from(_Pos, [], S, K, Tr, _Path, Env) -> ret(S, K, Tr, Env);
all_from(Pos = {Id, I}, [G | Gs], S = #s{c = C, epoch = E, reads = Reads0, tok = Tok, learned = Learned}, K, Tr, Path, Env) ->
  case known_cont(Tok, Pos, C, Learned) of
    {true, Reads, Reason} ->
      fail(maps:merge(Path, Reason), maps:merge(Reads0, Reads), Learned, Tr, Env);
    false ->
      K1 = case Gs of [] -> K; _ -> [{conj, Id, I + 1, Gs, Path} | K] end,
      goal(G, S, K1, [{cont, Tok, Pos, E} | Tr], Path, Env)
  end.

%% A disjunction: a decision. The first alternative under which the whole
%% remaining search succeeds answers the query. An alternative that fails
%% for a reason this decision is not part of fails the decision at once,
%% since the same failure exists under every other alternative; otherwise
%% the next alternative is tried with what the failed one learned, and the
%% reasons and reads of all of them are the reason the decision fails.
-spec any_of([goal()], s(), k(), trail(), reason(), env()) -> boolean().
any_of([], S, _K, Tr, Path, Env) -> fail(Path, S, Tr, Env);
any_of(Goals, S, K, Tr, Path, Env) ->
  D = erlang:unique_integer([positive]),
  decide(Goals, S, K, Tr, Path, D, #{}, S#s.reads, Env).

-spec decide([goal()], s(), k(), trail(), reason(), integer(), reason(), reads(), env()) -> boolean().
decide([], #s{learned = Learned}, _K, Tr, _Path, D, Acc, Reads, Env) ->
  fail(maps:remove(D, Acc), Reads, Learned, Tr, Env);
decide([G | Gs], S, K, Tr, Path, D, Acc, Reads, Env) ->
  goal(G, S, K, [{decide, Gs, S, K, Path, D, Acc, Reads} | Tr], Path#{D => []}, Env).

%% --- the variable level -----------------------------------------------------

%% Make the node T empty under C. One activation: it reads into a fresh read
%% set, hands its reads on when it exits, and if it fails before it ever
%% exited, {T, the pieces it read that predate it} is learned.
-spec empty(ty:type(), s(), k(), trail(), reason(), env()) -> boolean().
empty(T, S, K, Tr, Path, Env) ->
  case {ty_node:empty(), ty_node:any()} of
    {T, _} -> ret(S, K, Tr, Env);
    {_, T} -> fail(Path, S, Tr, Env);
    _ -> empty_node(T, S, K, Tr, Path, Env)
  end.

-spec empty_node(ty:type(), s(), k(), trail(), reason(), env()) -> boolean().
empty_node(T, S = #s{c = C, x = X, epoch = E0, reads = Reads0, tok = Tok0, learned = Learned0}, K, Tr, Path, Env = #env{fixed = Fixed}) ->
  case X of
    #{{node, T} := _} -> ret(S, K, Tr, Env);
    _ ->
      case is_ground(T, Fixed) of
        true ->
          case ty_node:is_empty(T) of
            true -> ret(S, K, Tr, Env);
            false -> fail(Path, S, Tr, Env)
          end;
        false ->
          case known_failure(T, Fixed, C) of
            {true, Reads, Reason} ->
              fail(maps:merge(Path, Reason), maps:merge(Reads0, Reads), Learned0, Tr, Env);
            false ->
              Tok = erlang:unique_integer([positive]),
              Prepared = ty_node:cached({pike_lines, T, Fixed}, fun() -> prepare(ty_node:lines(T), Fixed) end),
              all_of({lines, T}, Prepared, S#s{x = X#{{node, T} => []}, reads = #{}, tok = Tok},
                     [{exit, Reads0, Tok0, Tok} | K], [{activation, T, Tok, E0, Reads0} | Tr], Path, Env)
          end
      end
  end.

%% The lines of a node, prepared once per node and set of monomorphic
%% variables: a line with a polymorphic variable is its one-sided bound by
%% the NTLV rule -- the smallest such variable singled out against the rest
%% of the line -- and a line without one is its leaf, whose monomorphic
%% variables are eliminated (Part 1, Lemma C.3/C.11). Leaves go first: they
%% are the only lines that can fail on their own.
%% A leaf is prepared too: a leaf one of whose basic kinds is not empty is a
%% dead line, which goes first since it fails on its own; otherwise the
%% lines of its structured components, each a tuple, function or map line.
-type component() :: {tuple, tuple_dnf_line()} | {function, function_dnf_line()} | {map, map_dnf_line()}.
-type tuple_dnf_line() :: {[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}.
-type function_dnf_line() :: {[ty_function:type()], [ty_function:type()], ty_bool:type()}.
-type map_dnf_line() :: {[ty_map:type()], [ty_map:type()], ty_bool:type()}.
-type prepared() :: dead | {leaf, integer(), [component()]}
                  | {upper, variable(), ty:type()} | {lower, variable(), ty:type()}.
-spec prepare([{[variable()], [variable()], ty_rec:type()}], monomorphic_variables()) -> [prepared()].
prepare(Lines, Fixed) ->
  Prepared = [prepare_line(L, Fixed) || L <- Lines],
  {Dead, Rest} = lists:partition(fun(dead) -> true; (_) -> false end, Prepared),
  {Leaves, Bounds} = lists:partition(fun({leaf, _, _}) -> true; (_) -> false end, Rest),
  Dead ++ Leaves ++ Bounds.

-spec prepare_line({[variable()], [variable()], ty_rec:type()}, monomorphic_variables()) -> prepared().
prepare_line({[], [], Leaf}, _Fixed) -> prepare_leaf(Leaf);
prepare_line({P, N, Leaf}, Fixed) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} -> {upper, V, ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf))};
    {{neg, V}, _} -> {lower, V, ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf))};
    {{{delta, _}, _}, _} -> prepare_leaf(Leaf)
  end.

-spec prepare_leaf(ty_rec:type()) -> prepared().
prepare_leaf(any) -> dead;
prepare_leaf(empty) -> {leaf, erlang:unique_integer([positive]), []};
prepare_leaf(TyRec) ->
  case basic_empty(TyRec) of
    false -> dead;
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
      {leaf, erlang:unique_integer([positive]), Components}
  end.

%% A type all of whose variables are monomorphic is a constant for tallying:
%% the subtyping engine decides it, treating those variables as atoms exactly
%% as the delta rule of normalize_line does.
-spec is_ground(ty:type(), monomorphic_variables()) -> boolean().
is_ground(T, Fixed) when map_size(Fixed) =:= 0 ->
  sets:is_empty(ty_node:all_variables(T));
is_ground(T, Fixed) ->
  lists:all(fun(V) -> maps:is_key(V, Fixed) end, sets:to_list(ty_node:all_variables(T))).

%% alpha <= U, a piece depending on Path. A piece the current upper bound
%% already implies changes nothing. Otherwise every lower piece must fit
%% under the new one: one consequence per pair, each reading the lower piece.
-spec bound_upper(variable(), ty:type(), s(), k(), trail(), reason(), env()) -> boolean().
bound_upper(V, U, S = #s{c = C, epoch = E}, K, Tr, Path, Env) ->
  Empty = ty_node:empty(),
  case C of
    #{V := {CL, CU, Ls, Us}} ->
      case intersect_bound(U, CU, Env) of
        CU -> ret(S, K, Tr, Env);
        U1 ->
          S1 = S#s{c = C#{V := {CL, U1, Ls, [{U, Path, E} | Us]}}, epoch = E + 1},
          consequences({upper, V, U}, [{ty_node:difference(L, U), maps:merge(RL, Path), {V, lower, L}, EL}
                                        || {L, RL, EL} <- Ls], S1, K, Tr, Env)
      end;
    _ ->
      ret(S#s{c = C#{V => {Empty, U, [], [{U, Path, E}]}}, epoch = E + 1}, K, Tr, Env)
  end.

%% L <= alpha, symmetric: the new lower piece must fit under every upper piece.
-spec bound_lower(variable(), ty:type(), s(), k(), trail(), reason(), env()) -> boolean().
bound_lower(V, L, S = #s{c = C, epoch = E}, K, Tr, Path, Env) ->
  Any = ty_node:any(),
  case C of
    #{V := {CL, CU, Ls, Us}} ->
      case union_bound(L, CL, Env) of
        CL -> ret(S, K, Tr, Env);
        L1 ->
          S1 = S#s{c = C#{V := {L1, CU, [{L, Path, E} | Ls], Us}}, epoch = E + 1},
          consequences({lower, V, L}, [{ty_node:difference(L, U), maps:merge(RU, Path), {V, upper, U}, EU}
                                        || {U, RU, EU} <- Us], S1, K, Tr, Env)
      end;
    _ ->
      ret(S#s{c = C#{V => {L, Any, [{L, Path, E}], []}}, epoch = E + 1}, K, Tr, Env)
  end.

%% The consequences of a new piece: for every piece on the other side, the
%% pair must satisfy lower <= upper. Each is an empty goal under the two
%% pieces' reasons, and reads the piece it was paired with.
-spec consequences(term(), [{ty:type(), reason(), read(), epoch()}], s(), k(), trail(), env()) -> boolean().
consequences(Id, Pairs, S, K, Tr, Env) ->
  Empty = ty_node:empty(),
  % a pair whose difference is the empty node holds by itself: no goal, no read
  case [{consequence, T, Path, Read, Epoch} || {T, Path, Read, Epoch} <- Pairs, T =/= Empty] of
    [] -> ret(S, K, Tr, Env);
    Goals -> all_of(Id, Goals, S, K, Tr, #{}, Env)
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

-spec basic_empty(ty_rec:type_record()) -> boolean().
basic_empty(TyRec) ->
  element(1, dnf_ty_predefined:is_empty(ty_rec:pi(TyRec, dnf_ty_predefined), #{}))
    andalso element(1, dnf_ty_atom:is_empty(ty_rec:pi(TyRec, dnf_ty_atom), #{}))
    andalso element(1, dnf_ty_interval:is_empty(ty_rec:pi(TyRec, dnf_ty_interval), #{})).

%% One line of a tuple (or list, bitstring) DNF, as dnf_ty_tuple:normalize_line.
-spec tuple_line(tuple_dnf_line(), s(), k(), trail(), reason(), env()) -> boolean().
tuple_line({[], [], _}, S, _K, Tr, Path, Env) ->
  fail(Path, S, Tr, Env); % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, S, K, Tr, Path, Env) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, S, K, Tr, Path, Env);
tuple_line({Pos, Neg, _}, S, K, Tr, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, S, K, Tr, Path, Env).

%% One line of a map DNF, as dnf_ty_map:normalize_line: maps are encoded as a
%% pair of a tuple part and a function part, with its own any.
-spec map_line(map_dnf_line(), s(), k(), trail(), reason(), env()) -> boolean().
map_line({[], [], _}, S, _K, Tr, Path, Env) -> fail(Path, S, Tr, Env);
map_line({[], Neg = [_ | _], Leaf}, S, K, Tr, Path, Env) ->
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  map_line({[ty_map:map(P1, P2)], Neg, Leaf}, S, K, Tr, Path, Env);
map_line({Pos, Neg, _}, S, K, Tr, Path, Env) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, S, K, Tr, Path, Env).

%% S1 x .. x Sn \ (N1 | .. | Nk) <= 0, as dnf_ty_tuple:phi_norm: some Si is
%% empty, or for the first negative tuple N1, for every component i the
%% product with Si \ N1_i is empty without N1. One decision, unless a
%% component is already empty on this path.
-spec phi([ty:type()], [ty_tuple:type()], s(), k(), trail(), reason(), env()) -> boolean().
phi(BigS, Neg, S = #s{x = X}, K, Tr, Path, Env) ->
  Key = {phi, BigS, Neg},
  case X of
    #{Key := _} -> ret(S, K, Tr, Env);
    _ ->
      case lists:any(fun(Si) -> maps:is_key({node, Si}, X) end, BigS) of
        true -> ret(S#s{x = X#{Key => []}}, K, Tr, Env);
        false ->
          Components = [{empty, Si} || Si <- BigS],
          Alternatives = case Neg of
            [] -> Components;
            [Ty | N] -> Components ++ [{all, {Key, split}, without(BigS, ty_tuple:components(Ty), 1, N)}]
          end,
          any_of(Alternatives, S, [{achieve, Key} | K], Tr, Path, Env)
      end
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
%% which needs T1 inside the union of the domains and explore to hold.
%% Which negative arrow is one decision.
-spec function_line(function_dnf_line(), s(), k(), trail(), reason(), env()) -> boolean().
function_line({Pos, Neg, _}, S, K, Tr, Path, Env) ->
  Dom = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  NotDom = ty_node:negate(Dom),
  Alternatives =
    [{all, {function_line, Pos, F},
      [{empty, ty_node:intersect(ty_function:domain(F), NotDom)},
       {explore, ty_function:domain(F), ty_node:negate(ty_function:codomain(F)), Pos}]}
     || F <- Neg],
  any_of(Alternatives, S, K, Tr, Path, Env).

%% As dnf_ty_function:explore_function_norm: T1 empty, or T2 empty, or the
%% positive arrow S1 -> S2 is split off on both sides. One decision, unless
%% T1 or T2 is already empty on this path.
-spec explore(ty:type(), ty:type(), [ty_function:type()], s(), k(), trail(), reason(), env()) -> boolean().
explore(T1, T2, P, S = #s{x = X}, K, Tr, Path, Env) ->
  Key = {explore, T1, T2, P},
  case X of
    #{Key := _} -> ret(S, K, Tr, Env);
    _ ->
      case maps:is_key({node, T1}, X) orelse maps:is_key({node, T2}, X) of
        true -> ret(S#s{x = X#{Key => []}}, K, Tr, Env);
        false ->
          Split = case P of
            [] -> [];
            [F | Ps] ->
              S1 = ty_function:domain(F),
              S2 = ty_function:codomain(F),
              [{all, {Key, split},
                [{explore, T1, ty_node:intersect(T2, S2), Ps},
                 {explore, ty_node:difference(T1, S1), T2, Ps}]}]
          end,
          any_of([{empty, T1}, {empty, T2} | Split], S, [{achieve, Key} | K], Tr, Path, Env)
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
