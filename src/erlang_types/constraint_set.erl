-module(constraint_set).

-define(LAZY(Term), fun() -> Term end).

% utility
-export([
    sat/0,
    unsat/0,
    singleton/1,
    len/1,
    map/2,
    fold/3,
    any/2,
    all/2,
    filter/2
]).

-export([
  meet/3, meet/4,
  join/3, join/4,
  saturate/3, saturate/4,
  meet_saturate/4,
  norm/4,
  memo_new/0,
  is_trivial_sat/1
]).

-export_type([
  set_of_constraint_sets/0, 
  constraint_set/0,
  memo/0
]).

% API
-include("constraints.hrl").
-include("etylizer.hrl").
-include("sanity.hrl").

-type cache() :: #{{ty:type(), ty:type()} => []}.


-spec is_trivial_sat(set_of_constraint_sets()) -> boolean().
is_trivial_sat([[]]) -> true;
is_trivial_sat(_) -> false.

-spec sat() -> set_of_constraint_sets().
sat() -> [[]].

-spec unsat() -> set_of_constraint_sets().
unsat() -> [].

-spec singleton(constraint_set()) -> set_of_constraint_sets().
singleton(Cs) -> [Cs].

-spec len(set_of_constraint_sets()) -> non_neg_integer().
len(Cs) -> length(Cs).

-spec fold(fun((constraint_set(), Acc) -> Acc), Acc, S) -> Acc when S :: set_of_constraint_sets().
fold(F, Accumulator, Socs) ->
    lists:foldl(fun(Cs, Acc) -> F(Cs, Acc) end, Accumulator, Socs).

-spec map(fun((constraint_set()) -> B), S) -> [B] when S :: set_of_constraint_sets().
map(F, Socs) ->
    lists:map(fun(Cs) -> F(Cs) end, Socs).

-spec any(fun((constraint_set()) -> boolean()), set_of_constraint_sets()) -> boolean().
any(Pred, Socs) ->
    lists:any(Pred, Socs).

-spec all(fun((constraint_set()) -> boolean()), set_of_constraint_sets()) -> boolean().
all(Pred, Socs) ->
    lists:all(Pred, Socs).

-spec filter(fun((constraint_set()) -> boolean()), S) -> S when S :: set_of_constraint_sets().
filter(Pred, Socs) ->
    lists:filter(Pred, Socs).


% sets of constraint sets

%% --- per-problem memo --------------------------------------------------------
%% The search asks the engine the same questions over and over: subsumption
%% compares the same pair of bounds across every pair of constraint sets that
%% carry them, and a merged constraint's satisfiability check is the same
%% normalization its later expansion needs. The engine's caches answer those
%% repeats, but every repeat is still an ETS round-trip. The memo answers a
%% repeated question from a map lookup instead, so the engine is asked once per
%% distinct question per problem. It is threaded explicitly: the search creates
%% one per tally call, every operation takes it and returns it updated, and the
%% 3-arity entry points run with a fresh one and drop it, for callers that are
%% not a search. It also pins the empty and any nodes, which the identity fast
%% paths would otherwise re-cons through ETS on every use.
-type memo() :: #{empty => ty:type(), any => ty:type(),
                  {leq, ty:type(), ty:type()} => boolean(),
                  {empty, ty:type()} => boolean(),
                  {norm, ty:type(), ty:type()} => set_of_constraint_sets()}.

-spec memo_new() -> memo().
memo_new() -> #{}.

%% The empty and any nodes, consed on first use and pinned in the memo.
-spec pins(memo()) -> {ty:type(), ty:type(), memo()}.
pins(M = #{empty := Empty, any := Any}) -> {Empty, Any, M};
pins(M) ->
  Empty = ty_node:empty(),
  Any = ty_node:any(),
  {Empty, Any, M#{empty => Empty, any => Any}}.

-spec meet(S, S, monomorphic_variables()) -> S when S :: set_of_constraint_sets().
meet(S1, S2, Fixed) ->
  {S, _} = meet(S1, S2, Fixed, memo_new()),
  S.

-spec meet(S, S, monomorphic_variables(), memo()) -> {S, memo()} when S :: set_of_constraint_sets().
meet([], _, _, M) -> {[], M};
meet(_, [], _, M) -> {[], M};
meet([[]], Set2, _, M) -> {Set2, M};
meet(Set1, [[]], _, M) -> {Set1, M};
%% Idempotency: meet(S, S) = S. The cartesian product generates joins
%% join(c, c') for c, c' in S. join(c, c) = c is in S; join(c, c') for c≠c' is
%% strictly tighter and subsumed by both c and c' (which are in S). Minimize
%% keeps the most general → returns S.
meet(Same, Same, _, M) -> {Same, M};
meet(S1, S2, Fixed, M) ->
  %% Set-equality (modulo order) is the same as term-equality for sorted reps.
  %% Sort+compare is O(n log n + n) — cheap for small n which dominates here.
  case lists:sort(S1) =:= lists:sort(S2) of
    true -> {S1, M};
    false -> meet_full(S1, S2, Fixed, M)
  end.

%% Incremental subsumption-during-construction. Walks the |S1|×|S2| Cartesian
%% product but never builds it as a list — and for each pair, refuses to add
%% if the accumulator already has something smaller (so the result stays
%% minimal as we go). Joining two satisfiable sets can only fail on a merged
%% bound pair, which join_constraint_sets checks as it goes.
-spec meet_full(S, S, monomorphic_variables(), memo()) -> {S, memo()} when S :: set_of_constraint_sets().
meet_full(S1, S2, Fixed, M0) ->
  lists:foldl(
    fun(C1, Acc1) ->
        lists:foldl(
          fun(C2, {Acc, M}) ->
              case join_constraint_sets(C1, C2, Fixed, M) of
                {unsat, M1} -> {Acc, M1};
                {NewCs, M1} -> add_minimal(NewCs, Acc, M1)
              end
          end, Acc1, S2)
    end, {[], M0}, S1).

%% Add NewCs to the minimal set Acc: dropped when something in Acc is smaller,
%% otherwise added, and whatever it subsumes removed.
-spec add_minimal(constraint_set(), S, memo()) -> {S, memo()} when S :: set_of_constraint_sets().
add_minimal(NewCs, Acc, M0) ->
  case has_smaller_constraint(NewCs, Acc, M0) of
    {true, M1} -> {Acc, M1};
    {false, M1} ->
      {Kept, M2} = lists:foldr(
        fun(C, {Ks, M}) ->
          case is_smaller(NewCs, C, M) of
            {true, Mx} -> {Ks, Mx};
            {false, Mx} -> {[C | Ks], Mx}
          end
        end, {[], M1}, Acc),
      {[NewCs | Kept], M2}
  end.

%% Meet two *saturated* solutions and saturate the result. A constraint that a
%% joined set inherits unchanged from either parent was expanded when that
%% parent was saturated, and the joined set -- whose bounds are only ever
%% tighter -- still implies whatever the expansion added. So only constraints
%% whose bounds were merged need expanding: each joined set's saturation cache
%% is seeded with the bound pairs of both parents. The product is pruned by
%% subsumption before saturating, as in meet/4.
-spec meet_saturate(S, S, monomorphic_variables(), memo()) -> {S, memo()} when S :: set_of_constraint_sets().
meet_saturate([], _, _, M) -> {[], M};
meet_saturate(_, [], _, M) -> {[], M};
meet_saturate([[]], Set2, _, M) -> {Set2, M};
meet_saturate(Set1, [[]], _, M) -> {Set1, M};
meet_saturate(Same, Same, _, M) -> {Same, M};
meet_saturate(S1, S2, Fixed, M0) ->
  {Seeded, M1} = lists:foldl(
    fun(C1, Acc1) ->
        Seed1 = seed(C1, #{}),
        lists:foldl(
          fun(C2, {Acc, M}) ->
              case join_constraint_sets(C1, C2, Fixed, M) of
                {unsat, Mx} -> {Acc, Mx};
                {NewCs, Mx} -> add_minimal_seeded(NewCs, seed(C2, Seed1), Acc, Mx)
              end
          end, Acc1, S2)
    end, {[], M0}, S1),
  lists:foldl(
    fun(_, {[[]], M}) -> {[[]], M};
       ({Cs, Cache}, {AllS, M}) ->
         {Sat, Mx} = saturate(Cs, Fixed, Cache, M),
         join(AllS, Sat, Fixed, Mx)
    end, {[], M1}, Seeded).

%% add_minimal/3 over {constraint_set(), cache()} entries.
-spec add_minimal_seeded(constraint_set(), cache(), Acc, memo()) -> {Acc, memo()}
    when Acc :: [{constraint_set(), cache()}].
add_minimal_seeded(NewCs, Cache, Acc, M0) ->
  case has_smaller_constraint(NewCs, [Cs || {Cs, _} <- Acc], M0) of
    {true, M1} -> {Acc, M1};
    {false, M1} ->
      {Kept, M2} = lists:foldr(
        fun(E = {C, _}, {Ks, M}) ->
          case is_smaller(NewCs, C, M) of
            {true, Mx} -> {Ks, Mx};
            {false, Mx} -> {[E | Ks], Mx}
          end
        end, {[], M1}, Acc),
      {[{NewCs, Cache} | Kept], M2}
  end.

-spec seed(constraint_set(), cache()) -> cache().
seed(Cs, Cache) ->
  lists:foldl(fun({_Var, S, T}, C) -> C#{{S, T} => []} end, Cache, Cs).

-spec join(S, S, monomorphic_variables()) -> S when S :: set_of_constraint_sets().
join(S1, S2, Fixed) ->
  {S, _} = join(S1, S2, Fixed, memo_new()),
  S.

%% Every constraint set reaching join is satisfiable constraint by constraint:
%% normalize/2 emits single-bound constraints, and every merged bound pair is
%% checked in join_var_eq when it is created. Only subsumption is left to
%% decide.
-spec join(S, S, monomorphic_variables(), memo()) -> {S, memo()} when S :: set_of_constraint_sets().
join([[]], _Set2, _Fixed, M) -> {[[]], M};
join(_Set1, [[]], _Fixed, M) -> {[[]], M};
join([], Set, _Fixed, M) -> {Set, M};
join(Set, [], _Fixed, M) -> {Set, M};
join(S1, S2, _Fixed, M0) ->
  {S22, M1} = not_subsumed(S2, S1, M0),
  {S11, M2} = not_subsumed(S1, S22, M1),
  {lists:usort(S11 ++ S22), M2}.

%% The sets of Sets that no set of Against is smaller than.
-spec not_subsumed(S, S, memo()) -> {S, memo()} when S :: set_of_constraint_sets().
not_subsumed(Sets, Against, M0) ->
  lists:foldr(
    fun(Cs, {Keep, M}) ->
      case has_smaller_constraint(Cs, Against, M) of
        {true, Mx} -> {Keep, Mx};
        {false, Mx} -> {[Cs | Keep], Mx}
      end
    end, {[], M0}, Sets).

% step 2. from merge phase
% step 1. happens by construction automatically
-spec saturate(constraint_set(), monomorphic_variables(), cache()) -> set_of_constraint_sets().
saturate(C, FixedVariables, Cache) ->
  {S, _} = saturate(C, FixedVariables, Cache, memo_new()),
  S.

-spec saturate(constraint_set(), monomorphic_variables(), cache(), memo()) ->
    {set_of_constraint_sets(), memo()}.
saturate(C, FixedVariables, Cache, M0) ->
  case pick_bounds_in_c(C, Cache, M0) of
    {{_Var, S, T}, Cache1, M1} ->
      {Normed, M2} = norm(S, T, FixedVariables, M1),
      {NewS, M3} = meet([C], Normed, FixedVariables, M2),
      Cache2 = Cache1#{{S, T} => []},
      %% Short-circuit join-fold: once AllS = [[]] (trivially satisfied),
      %% remaining recursive saturate calls don't change the outcome — join
      %% absorbs them. Mirrors the andalso/orelse semantics of is_empty.
      lists:foldl(
        fun(_NewC, {[[]], M}) -> {[[]], M};
           (NewC, {AllS, M}) ->
             {NewMerged, Mx} = saturate(NewC, FixedVariables, Cache2, M),
             join(AllS, NewMerged, FixedVariables, Mx)
        end, {[], M3}, NewS);
    {none, _, M1} ->
      {[C], M1}
  end.

%% normalize(S \ T): the satisfiability of a bound pair and its expansion in
%% saturation are the same question.
-spec norm(ty:type(), ty:type(), monomorphic_variables(), memo()) ->
    {set_of_constraint_sets(), memo()}.
norm(S, T, Fixed, M) ->
  case M of
    #{{norm, S, T} := R} -> {R, M};
    _ ->
      R = ty_node:normalize(ty_node:difference(S, T), Fixed),
      {R, M#{{norm, S, T} => R}}
  end.

-spec is_empty_node(ty:type(), memo()) -> {boolean(), memo()}.
is_empty_node(S, M) ->
  case M of
    #{{empty, S} := R} -> {R, M};
    _ ->
      R = ty_node:is_empty(S),
      {R, M#{{empty, S} => R}}
  end.

% helper functions

%% Joining two satisfiable constraint sets can only fail on a variable both
%% constrain, whose merged bounds are new. Those are checked here, as they are
%% made, and the join stops at the first that cannot hold; every other
%% constraint is inherited and was checked when its set was built.
-spec join_constraint_sets(Cs, Cs, monomorphic_variables(), memo()) -> {unsat | Cs, memo()}
    when Cs :: constraint_set().
join_constraint_sets([], L, _, M) -> {L, M};
join_constraint_sets(L, [], _, M) -> {L, M};
join_constraint_sets(LeftAll = [NextLeft = {V1, T1, T2} | C1], RightAll = [NextRight = {V2, S1, S2} | C2], Fixed, M) ->
  case ty_variable:compare(V1, V2) of
    eq ->
      join_var_eq(V1, T1, S1, T2, S2, C1, C2, Fixed, M);
    lt ->
      cons_sat(NextLeft, join_constraint_sets(C1, RightAll, Fixed, M));
    gt ->
      cons_sat(NextRight, join_constraint_sets(C2, LeftAll, Fixed, M))
  end.

-spec cons_sat(constraint(), {unsat | constraint_set(), memo()}) -> {unsat | constraint_set(), memo()}.
cons_sat(_C, {unsat, M}) -> {unsat, M};
cons_sat(C, {Cs, M}) -> {[C | Cs], M}.

-spec join_var_eq(variable(), Ty, Ty, Ty, Ty, Cs, Cs, monomorphic_variables(), memo()) -> {unsat | Cs, memo()}
    when Ty :: ty:type(), Cs :: constraint_set().
join_var_eq(Var, T1, S1, T2, S2, C1, C2, Fixed, M0) ->
  {Empty, Any, M1} = pins(M0),
  Lower = union_bound(T1, S1, Empty),
  Upper = intersect_bound(T2, S2, Any),
  %% Merged bounds equal to one side's are that side's constraint, already
  %% checked; only a genuinely new pair of bounds can be unsatisfiable.
  Known = ({Lower, Upper} =:= {T1, T2}) orelse ({Lower, Upper} =:= {S1, S2}),
  case Known of
    true ->
      cons_sat({Var, Lower, Upper}, join_constraint_sets(C1, C2, Fixed, M1));
    false ->
      case is_unsatisfiable({Var, Lower, Upper}, Fixed, M1) of
        {true, M2} -> {unsat, M2};
        {false, M2} -> cons_sat({Var, Lower, Upper}, join_constraint_sets(C1, C2, Fixed, M2))
      end
  end.

%% Identical nodes need no engine call; the empty and any nodes are units.
-spec union_bound(T, T, T) -> T when T :: ty:type().
union_bound(A, A, _Empty) -> A;
union_bound(Empty, B, Empty) -> B;
union_bound(A, Empty, Empty) -> A;
union_bound(A, B, _Empty) -> ty:union(A, B).

-spec intersect_bound(T, T, T) -> T when T :: ty:type().
intersect_bound(A, A, _Any) -> A;
intersect_bound(Any, B, Any) -> B;
intersect_bound(A, Any, Any) -> A;
intersect_bound(A, B, _Any) -> ty:intersect(A, B).

-spec is_unsatisfiable(constraint(), monomorphic_variables(), memo()) -> {boolean(), memo()}.
is_unsatisfiable({_Var, L, R}, _Fixed, M) when L =:= R ->
  % Type nodes are hash-consed, so equal ids are equal types and L\R is empty,
  % which normalizes to [[]] -- trivially satisfiable, never to [].
  {false, M};
is_unsatisfiable({_Var, L, R}, Fixed, M0) ->
  {Normed, M1} = norm(L, R, Fixed, M0),
  {Normed =:= [], M1}.

%% Whether some set in S is smaller than Con.
-spec has_smaller_constraint(constraint_set(), set_of_constraint_sets()) -> boolean().
has_smaller_constraint(Con, S) ->
  {R, _} = has_smaller_constraint(Con, S, memo_new()),
  R.

-spec has_smaller_constraint(constraint_set(), set_of_constraint_sets(), memo()) -> {boolean(), memo()}.
has_smaller_constraint(_Con, [], M) -> {false, M};
has_smaller_constraint(Con, [C | S], M0) ->
  case is_smaller(C, Con, M0) of
    {true, M1} -> {true, M1};
    {false, M1} -> has_smaller_constraint(Con, S, M1)
  end.

% leq(X, X) holds without asking the type engine: nodes are hash-consed, so
% identical ids are identical types. The constraint sets in one disjunction are
% built by meeting the same base sets, so most of their bounds are literally the
% same node and this pointer test replaces a difference plus an emptiness check.
% Beyond identity, an empty lower or an any upper bound decide the question
% without the engine, and every other answer is memoized for the problem.
-spec sub(T, T, memo()) -> {boolean(), memo()} when T :: ty_node:type().
sub(X, X, M) -> {true, M};
sub(X, Y, M0) ->
  case M0 of
    #{{leq, X, Y} := R} -> {R, M0};
    _ ->
      {Empty, Any, M1} = pins(M0),
      case X =:= Empty orelse Y =:= Any of
        true -> {true, M1};
        false ->
          R = ty_node:leq(X, Y),
          {R, M1#{{leq, X, Y} => R}}
      end
  end.

% C1 and C2 are sorted by variable order
-spec is_smaller(constraint_set(), constraint_set()) -> boolean().
is_smaller(C1, C2) ->
  {R, _} = is_smaller(C1, C2, memo_new()),
  R.

-spec is_smaller(constraint_set(), constraint_set(), memo()) -> {boolean(), memo()}.
is_smaller([], _C2, M) -> {true, M};
is_smaller(_C1, [], M) -> {false, M};
is_smaller(All = [{V1, T1, T2} | C1], [{V2, S1, S2} | C2], M0) ->
  case ty_variable:compare(V1, V2) of
    eq ->
      case sub(T1, S1, M0) of
        {false, M1} -> {false, M1};
        {true, M1} ->
          case sub(S2, T2, M1) of
            {false, M2} -> {false, M2};
            {true, M2} -> is_smaller(C1, C2, M2)
          end
      end;
    lt ->
      % V1 is not in the other set
      % not smaller
      {false, M0};
    gt ->
      is_smaller(All, C2, M0)
  end.

%% The saturation cache is keyed by the bound pair, which is all the expansion
%% depends on, and is consulted before any engine call; a pair found trivially
%% satisfied is cached too, so on the next level it costs a map lookup rather
%% than an emptiness check.
-spec pick_bounds_in_c(constraint_set(), cache(), memo()) -> {none | constraint(), cache(), memo()}.
pick_bounds_in_c([], Cache, M) -> {none, Cache, M};
pick_bounds_in_c([{Var, S, T} | Cs], Cache, M0) ->
  case Cache of
    #{{S, T} := _} ->
      pick_bounds_in_c(Cs, Cache, M0);
    _ ->
      % The empty lower bound and the any upper bound are consed nodes, so the
      % common cases are decided by identity before any emptiness check.
      {Empty, Any, M1} = pins(M0),
      case S =:= Empty orelse T =:= Any of
        true ->
          pick_bounds_in_c(Cs, Cache#{{S, T} => []}, M1);
        false ->
          case is_empty_node(S, M1) of
            {true, M2} -> pick_bounds_in_c(Cs, Cache#{{S, T} => []}, M2);
            {false, M2} ->
              case sub(Any, T, M2) of
                {true, M3} -> pick_bounds_in_c(Cs, Cache#{{S, T} => []}, M3);
                {false, M3} -> {{Var, S, T}, Cache, M3}
              end
          end
      end
  end.

-spec minimize(S) -> S when S :: set_of_constraint_sets().
minimize(S) -> minimize(S, S).

-spec minimize(S, S) -> S when S :: set_of_constraint_sets().
minimize([], Result) -> Result;
minimize([Cs | Others], All) ->
  NewS = All -- [Cs],
  case has_smaller_constraint(Cs, NewS) of
    true ->
      ?assert_pattern(true, length(NewS) < length(All)),
      minimize(NewS, NewS);
    _ -> minimize(Others, All)
  end.

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

% TODO why does Dialyzer complain that L. 256 has no return?
-dialyzer({no_return, [smaller_test/0]}).
-spec smaller_test() -> _.
smaller_test() ->
  global_state:with_new_state(fun() ->
    % {(β≤0)} <: {(β≤0) (β≤α)}
    Alpha = ty_variable:new_with_name(alpha),
    Beta = ty_variable:new_with_name(beta),
    C1 = [{Beta, ty:empty(), ty:empty()}],
    % β < α according to variable order and constraint sets are ordered
    C2 = [{Beta, ty:empty(), ty:empty()}, {Alpha, ty:variable(Beta), ty:any()}],

    true = is_smaller(C1, C2),
    false = is_smaller(C2, C1)
  end).

-spec smaller2_test() -> _.
smaller2_test() ->
  global_state:with_new_state(fun() ->
    % C1 :: {(atom≤β≤1)}
    % C2 :: {(   1≤β≤1)}
    Beta = ty_variable:new_with_name(beta),
    Atom = ty:atom(), % replacement for bool
    C1 = [{Beta, Atom,     ty:any()}],
    C2 = [{Beta, ty:any(), ty:any()}],

    % C1 =< C2 iff
    %        (beta, >=, atom) in C1
    %     => (beta, >=, 1)    in C2 such that 1 >= atom (true)
    true = is_smaller(C1, C2)
  end).

-spec paper_example_test() -> _.
paper_example_test() ->
  global_state:with_new_state(fun() ->
    % C1 :: {(β≤α≤1)    (0≤β≤0)} :: {(β≤α)    (β≤0)}
    % C2 :: {(β≤α≤1) (atom≤β≤1)} :: {(atom≤β) (β≤α)}
    % C3 :: {           (0≤β≤0)} :: {(0≤β)         }
    % C4 :: {(β≤α≤1)    (1≤β≤1)} :: {(1≤β)    (β≤α)}
    Alpha = ty_variable:new_with_name(alpha),
    Beta = ty_variable:new_with_name(beta),
    BetaTy = ty:variable(Beta),
    Atom = ty:atom(),
    C1 = [{Beta, ty:empty(), ty:empty()}, {Alpha, BetaTy, ty:any()} ],
    C2 = [{Beta, Atom, ty:any()}, {Alpha, BetaTy, ty:any()}],
    C3 = [{Beta, ty:empty(), ty:empty()}],
    C4 = [{Beta, ty:any(), ty:any()}, {Alpha, BetaTy, ty:any()}],

    true = is_smaller(C2, C4),
    false = is_smaller(C4, C2),

    true = is_smaller(C3, C1),
    false = is_smaller(C1, C3),

    % proper reduce test, C4 is redundant
    S = [C2, C4, C1],
    Min = minimize(S),
    true = length(Min) =:= 2
  end).

-endif.
