-module(etally).

-define(TY, ty_node).


-export_type([monomorphic_variables/0, tally_solutions/0, tally_solutions_nonempty/0]).

-export([
  tally/1,
  tally/2,
  is_tally_satisfiable/2,
  tally_saturate/2,
  is_satisfiable_v2/2
]).

-include("etylizer.hrl").
-include("sanity.hrl").
-include("constraints.hrl").

-define(TALLY_DEFAULT(), is_satisfiable_v6).

-type normalized_set_of_constraint_sets() :: set_of_constraint_sets(). % normalized set of constraint sets
-type solutions() :: set_of_constraint_sets(). % saturated set of constraint sets
-type input_constraint() :: {ty:type(), ty:type()}.
-type input_constraints() :: [input_constraint()].
-type tally_solutions() :: [#{variable() => ty:type()}].
-type tally_solutions_nonempty() :: [#{variable() => ty:type()}, ...].

% early return if constraints are found to be satisfiable
% does not solve the equations
-spec is_tally_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_tally_satisfiable(Constraints, MonomorphicVariables) ->
  case os:getenv(?assert_type(string:to_upper("TALLY"), nonempty_string())) of
    "v1" -> is_satisfiable_v1(Constraints, MonomorphicVariables);
    "v2" -> is_satisfiable_v2(Constraints, MonomorphicVariables);
    "v3" -> is_satisfiable_v3(Constraints, MonomorphicVariables);
    "v4" -> is_satisfiable_v4(Constraints, MonomorphicVariables);
    "v5" -> is_satisfiable_v5(Constraints, MonomorphicVariables);
    "v6" -> is_satisfiable_v6(Constraints, MonomorphicVariables);
    _ -> ?TALLY_DEFAULT()(Constraints, MonomorphicVariables)
  end.



% CDuce version without the solve phase, almost paper version
% normalize & first part of merge at the same time,
% then saturation of upper and lower bounds at the end
-spec is_satisfiable_v1(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v1(Constraints, MonomorphicVariables) ->
  % io:format(user,"~n~n=== Step 1: Normalize ~p constraints~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Constraints), MonomorphicVariables]),
  Normalized = ?TIME(tally_sat_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  % io:format(user,"~n=== Step 2: Saturate~n~p sets of constraint sets~n", [length(Normalized)]),
  Saturated = ?TIME(tally_sat_saturate, tally_saturate_until_satisfiable(Normalized, MonomorphicVariables)),
  % sanity against full tally calculation
  ?SANITY(tally_satisfiable_sound, case {tally_saturate(Normalized, MonomorphicVariables), Saturated} of {[], false} -> ok; {[_ | _], true} -> ok end),
  Saturated.

-spec tally_saturate_until_satisfiable(normalized_set_of_constraint_sets(), monomorphic_variables()) -> boolean().
tally_saturate_until_satisfiable(Normalized, MonomorphicVariables) ->
  lists:any(
    fun(ConstraintSet) -> 
      case constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}) of 
        [] -> false; 
        _ -> true 
      end 
    end, Normalized).

% slice constraints and merge result, no order
-spec is_satisfiable_v2(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v2(Constraints, MonomorphicVariables) ->
  Z = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints],
  case lists:all(fun([[]]) -> true; (_) -> false end, Z) of
    true -> true;
    _ ->
      [S | Ss] =  ?assert_pattern([_ | _], Z),
      Z2 = lists:foldl(fun(E, E2) -> tally_saturate(constraint_set:meet(E, E2, MonomorphicVariables), MonomorphicVariables) end, S, Ss),
      case Z2 of
        [] -> false;
        _ -> true
      end
  end.

% slice constraints and merge single solutions first, then multiple solutions last
-spec is_satisfiable_v3(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v3(Constraints, MonomorphicVariables) ->
  Z = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints],
  case lists:all(fun([[]]) -> true; (_) -> false end, Z) of
    true -> true;
    _ ->
      All0 = Z,
      NotSat = [X || X <- All0, X == []],
      case length(NotSat) > 0 of
        true -> false;
        _ ->
          All = [X || X <- All0, X /= [[]]], 
          All1 = [X || X <- All, length(X) == 1],

          SimpleSat = lists:foldl(fun(E, E2) -> tally_saturate(constraint_set:meet(E, E2, MonomorphicVariables), MonomorphicVariables) end, [[]], All1),
          case SimpleSat of
            [] -> false;
            _ -> 
              All2 = [X || X <- All, length(X) > 1],
              case length(All2) of
                0 -> true;
                _ ->
                  % io:format("Got ~p complex~n", [length(All2)]),
                  % io:format("~n~p~n", [All2]),
                  ComplexSat = lists:foldl(fun(E, E2) -> tally_saturate(constraint_set:meet(E, E2, MonomorphicVariables), MonomorphicVariables) end, SimpleSat, All2),
                  % io:format("Complex in ~p ms~n", [T2]),

                  case ComplexSat of
                    [] -> false;
                    _ -> true
                  end
              end
          end
      end
  end.

-spec is_satisfiable_v4(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v4(Constraints, MonomorphicVariables) ->  
  % First, normalize and saturate each constraint individually
  InputSolutions = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints], % [solutions()] :: %
  
  case lists:all(fun([[]]) -> true; (_) -> false end, InputSolutions) of
    true -> true;
    false ->
      Red = [N || N <- InputSolutions, N /= [[]]],
      % then process each set of solutions individually
      process_input_solutions(Red, [[]], MonomorphicVariables)
  end.

-spec process_input_solutions(ToBeProcessed::[solutions()], CurrentResult::solutions(), monomorphic_variables()) -> boolean().
process_input_solutions([], _FinalResult, _MonoVars) -> 
  % No input solutions left to process, finished
  % FinalResult can't be []
  true;
process_input_solutions(TodoSols, CurrentResult, MonoVars) ->
  % T0 = erlang:system_time(millisecond),
  {SelectedSolution, NewResult} = find_least_increasing_solutions(TodoSols, CurrentResult, MonoVars),
  % io:format(user,"~p >> ~p sols (~p ms) (~p todos)~n~s~n", 
  %           [length(CurrentResult), length(NewResult), (erlang:system_time(millisecond)-T0), length(TodoSols), print(SelectedSolution)]
  %          ),
  case NewResult of
    [] -> false;
    _ -> process_input_solutions(TodoSols -- [SelectedSolution], NewResult, MonoVars)
  end.

%% Find the solution that increases solution count the least after saturation
-spec find_least_increasing_solutions(ToBeProcessed::[solutions(), ...], CurrentResult::solutions(), monomorphic_variables()) -> {solutions(), solutions()}.
find_least_increasing_solutions([Sol | Rest], Acc, MonoVars) ->
  MeetResult = constraint_set:meet(Sol, Acc, MonoVars),
  FirstSaturatedResult = tally_saturate(MeetResult, MonoVars),
  case {length(Acc), length(FirstSaturatedResult)} of
    {1, 1} -> {Sol, FirstSaturatedResult}; % special case
    _ ->
      % io:format(user,"Better than ~p -> ~p?~n", [length(Acc), length(FirstSaturatedResult)]),
      find_least_increasing_solutions(Rest, Acc, MonoVars, {Sol, FirstSaturatedResult})
  end.

-spec find_least_increasing_solutions(
        ToBeProcessed::[solutions()], 
        CurrentResult::solutions(), 
        monomorphic_variables(), 
        {solutions(), solutions()}) -> {solutions(), solutions()}.
find_least_increasing_solutions(All, Acc, MonoVars, Current) ->
  case lists:foldl(fun(E,A) -> do_find(E, A, Acc, MonoVars) end,  Current, All) of
    {shortcut, Z} -> Z;
    Z -> Z
  end.

-spec do_find(set_of_constraint_sets(), R, set_of_constraint_sets(), monomorphic_variables()) -> R when R :: {shortcut, {solutions(), solutions()}} | {solutions(), solutions()}.
do_find(_, Z = {shortcut, _}, _, _) -> Z;
do_find(S, {Cr, CurrentResult}, Acc, MonoVars) ->
      MeetResult = constraint_set:meet(S, Acc, MonoVars),
      SaturatedResult = tally_saturate(MeetResult, MonoVars),
      SatLen = constraint_set:len(SaturatedResult),
      CurLen = constraint_set:len(CurrentResult),
      if
        SatLen < CurLen -> 
          % io:format(user, "Found decreasing solution ~p (~p -> ~p)~n", [erlang:phash2(S), length(CurrentResult), length(SaturatedResult)]),
          {shortcut, {S, SaturatedResult}}; % This is the better solution (decrease sol count)
        CurLen < 3 andalso SatLen == CurLen -> 
          % io:format(user, "Found good solution ~p (~p)~n", [erlang:phash2(S), length(CurrentResult)]),
          {shortcut, {S, SaturatedResult}}; % This is a good solution (no increase and keeps sol count small)
        true -> {Cr, CurrentResult}
      end.

% -spec find_least_increasing_solutions(ToBeProcessed::[solutions()], CurrentResult::solutions(), monomorphic_variables(), {solutions(), solutions()}) -> {solutions(), solutions()}.
% find_least_increasing_solutions(All, Acc, MonoVars, Current) ->
%   case lists:foldl(fun
%     (_, Z = {shortcut, _}) -> Z;
%     (S, {Cr, CurrentResult}) -> 
%       MeetResult = constraint_set:meet(S, Acc, MonoVars),
%       SaturatedResult = tally_saturate(MeetResult, MonoVars),
%       if
%         length(SaturatedResult) < length(CurrentResult) -> 
%           % io:format(user, "Found decreasing solution ~p (~p -> ~p)~n", [erlang:phash2(S), length(CurrentResult), length(SaturatedResult)]),
%           {shortcut, {S, SaturatedResult}}; % This is the better solution (decrease sol count)
%        length(CurrentResult) < 3 andalso length(SaturatedResult) == length(CurrentResult) -> 
%           % io:format(user, "Found good solution ~p (~p)~n", [erlang:phash2(S), length(CurrentResult)]),
%           {shortcut, {S, SaturatedResult}}; % This is a good solution (no increase and keeps sol count small)
%         true -> {Cr, CurrentResult}
%       end
%                    end, Current, All) 
%   of
%     {shortcut, Z} -> Z;
%     Z -> Z
%   end.

% same slicing as v4, but the merge picks its next constraint by disjunction
% width instead of by trial-merging every candidate
-spec is_satisfiable_v5(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v5(Constraints, MonomorphicVariables) ->
  % First, normalize and saturate each constraint individually
  InputSolutions = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints],

  case lists:all(fun([[]]) -> true; (_) -> false end, InputSolutions) of
    true -> true;
    false ->
      Red = [N || N <- InputSolutions, N /= [[]]],
      merge_narrowest_first(order_narrow_first(Red), [[]], MonomorphicVariables)
  end.

%% Merging the per-constraint solutions is a fold, and which solution to fold in
%% next is a free choice. It decides two things at once: how wide the
%% accumulator gets, and how early a contradiction surfaces. v4 chooses by
%% trial-merging each remaining candidate and keeping whichever widens the
%% accumulator least -- a choice paid for in the type engine, and one that
%% optimises only for width. It never aims at a contradiction, so an
%% unsatisfiable query can build the whole product before reaching the
%% constraints that decide it.
%%
%% v5 keeps the slicing and merges narrowest disjunction first. That is unit
%% propagation: a width-1 solution is a deterministic consequence and merging it
%% cannot widen the accumulator, so draining those first keeps the accumulator
%% small *and* closes transitive variable bounds early, which is where
%% contradictions live. The merge exits as soon as the accumulator empties and
%% each step costs more the wider the accumulator is, so reaching the deciding
%% constraints early does not save a fraction of the work -- it skips the
%% expensive steps altogether.
%%
%% Ordering alone is not safe: it is greedy on a proxy it never checks, and a
%% sequence that looks narrow at every step can still explode. So the ordered
%% candidates are walked and the first that does not *widen* the accumulator is
%% taken, falling back to the least widening one. The guard bounds the damage;
%% the ordering is what makes the guarded walk stop after one or two candidates
%% instead of trying them all.
-spec merge_narrowest_first([solutions()], CurrentResult::solutions(),
                            monomorphic_variables()) -> boolean().
merge_narrowest_first([], _FinalResult, _MonoVars) ->
  % No input solutions left to merge, finished; FinalResult can't be []
  true;
merge_narrowest_first(TodoSols, CurrentResult, MonoVars) ->
  case walk_guarded(TodoSols, CurrentResult, constraint_set:len(CurrentResult), MonoVars, none) of
    unsat -> false;
    {NewResult, Selected} ->
      merge_narrowest_first(TodoSols -- [Selected], NewResult, MonoVars)
  end.

%% Sorted once, never recomputed: a solution's width is fixed at normalization
%% and the merge only removes entries, so re-sorting per step cannot change the
%% order. (A tiebreak on variable overlap with the accumulator, which *would*
%% change per step, was measured and made no difference -- the guard already
%% covers what it was meant to.)
-spec order_narrow_first([solutions()]) -> [solutions()].
order_narrow_first(Sols) ->
  lists:sort(fun(A, B) -> length(A) =< length(B) end, Sols).

%% Take the first candidate that does not widen the accumulator. A candidate that
%% empties it has answered the whole query, so the walk stops there.
%%
%% When widening is unavoidable -- which happens on satisfiable queries, where
%% every constraint must be merged and the accumulator has to grow -- no
%% candidate can satisfy the first test, so the walk would evaluate all of them
%% and keep the least widening. That is the expensive way to make a choice: each
%% trial is a full meet+saturate against a wide accumulator. Stop instead at the
%% first candidate that improves on the best seen so far, which is enough to
%% avoid a bad pick without pricing every alternative.
-spec walk_guarded([solutions()], solutions(), non_neg_integer(),
                   monomorphic_variables(), none | {solutions(), solutions()}) ->
        unsat | {solutions(), solutions()}.
walk_guarded([], _Acc, _AccLen, _MonoVars, none) -> unsat;
walk_guarded([], _Acc, _AccLen, _MonoVars, Best) -> Best;
walk_guarded([Sol | Rest], Acc, AccLen, MonoVars, Best) ->
  New = tally_saturate(constraint_set:meet(Sol, Acc, MonoVars), MonoVars),
  case constraint_set:len(New) of
    0 -> unsat;
    NewLen when NewLen =< AccLen -> {New, Sol};
    NewLen ->
      case Best of
        none -> walk_guarded(Rest, Acc, AccLen, MonoVars, {New, Sol});
        {BestSols, _} ->
          case NewLen < constraint_set:len(BestSols) of
            true -> {New, Sol};
            false -> walk_guarded(Rest, Acc, AccLen, MonoVars, Best)
          end
      end
  end.

%% =========================
%% v6: the same slicing as v4/v5, but the merge is a *pool* rather than a fold.
%%
%% Diagnosis that motivates it. v5's ordering (narrowest disjunction first) is
%% greedy on a proxy it never re-examines, and on one captured query it is
%% exactly wrong: the constraints that refute the query have the *widest*
%% disjunctions, so narrowest-first schedules them last. Merged blindly in that
%% order the accumulator runs 1,1,...,1,2,3,4,5,8,9,16,32,64,192,576,1728 --
%% every width-2/3 candidate multiplying it -- and only then do the width-5
%% candidates arrive and collapse it 1728 -> 48 -> 24 -> 12 -> 2 -> []. One
%% step at width 576 costs 33 s. v5 survives that only because walk_guarded
%% trial-merges and rejects: on that query the guard keeps the accumulator at
%% width 1 from the first step to the last.
%%
%% The reason a linear fold needs a guard is structural. It has a privileged
%% accumulator that everything else is merged into, so its width is a running
%% product: once wide it stays wide, every later step costs |Acc| * |Cand|, and
%% nothing but luck narrows it again. No property of a candidate that is
%% computable without the type engine can predict whether merging it widens the
%% accumulator -- except one: a width-1 disjunction can never widen anything.
%% That is the only free guarantee available, and it is why the guard exists.
%%
%% So v6 drops the privileged accumulator. The per-constraint solutions go into
%% a pool ordered by width and are merged pairwise: repeatedly take the
%% narrowest entry, merge it with the narrowest entry it shares a variable with,
%% and put the (saturated) result back into the pool at its new width. That
%% buys three things a fold cannot have:
%%
%%   * Width growth is spread, not compounded. A merge costs |A| * |B| where A
%%     is the pool minimum, so the cost of a step is bounded by the *pool*, not
%%     by a running product. A wide result immediately sinks in the width order
%%     and is not touched again until everything narrower has been consumed --
%%     the sinking is what the guard was faking.
%%
%%   * Unit propagation runs to a fixpoint for free. Width-1 entries sort first
%%     and are consumed first; merging one into a width-k entry yields at most
%%     k, and when it yields 1 that result re-enters the width-1 class and is
%%     consumed next. A fold that sorts once cannot see that, because a
%%     solution's static width never changes; v5 recovers it only by trying.
%%
%%   * Variable-disjoint merges are never chosen while any other merge is
%%     available. That one *is* provable. If A and B share no variable (bounds
%%     included) then joining a in A with b in B just concatenates two
%%     constraint lists: no bound is ever combined, so no new unsatisfiable
%%     constraint can appear, and neither can subsumption (A and B are already
%%     minimal, so is_smaller can only hold componentwise, i.e. for identical
%%     pairs). The merge is therefore *exactly* the |A| * |B| cartesian product:
%%     maximal cost, zero information. In the trajectory above every one of the
%%     multiplying steps was such a disjoint merge while informative,
%%     overlapping candidates were sitting in the queue.
%%
%% Merging is associative and commutative, so choosing pairs freely is sound;
%% the pool only ever changes *when* work happens, never *what* is computed.
%%
%% Measured over both self-check suites (1436 function checks): no function is
%% slower than 2 s under v6 where v4 or v5 is under 1 s, and the only regression
%% above 1.5x and 200 ms is subst:find_peelables/2 (0.27 s -> 1.06 s), more than
%% repaid inside its own file by subst:clean_cons/3 (5.04 s -> 3.17 s).
-spec is_satisfiable_v6(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v6(Constraints, MonomorphicVariables) ->
  % First, normalize and saturate each constraint individually
  InputSolutions = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints],

  case lists:all(fun([[]]) -> true; (_) -> false end, InputSolutions) of
    true -> true;
    false ->
      %% A single constraint that normalizes to no constraint set at all decides
      %% the query on its own. The fold-based versions discover this by meeting
      %% it into the accumulator; the pool has no accumulator, and a lone [] left
      %% in the pool would be read as satisfiable, so check for it up front.
      case lists:any(fun([]) -> true; (_) -> false end, InputSolutions) of
        true -> false;
        false ->
          Red = [N || N <- InputSolutions, N /= [[]]],
          merge_pool(build_pool(Red), MonomorphicVariables)
      end
  end.

%% A pool entry caches what the scheduler needs about a solution: its width and
%% the variables it mentions, the constrained ones and those occurring in bounds.
-type pool_entry() :: {non_neg_integer(), sets:set(variable()), solutions()}.

%% Variable sets are computed once per input solution and then *unioned* when two
%% entries merge. Merging can only lose variables (bounds are combined, never
%% invented), so the union over-approximates -- which is the harmless direction:
%% it can make the scheduler treat a disjoint pair as connected, never the
%% reverse. Recomputing them exactly after every merge is also much more
%% expensive than the scheduling it improves.
-spec build_pool([solutions()]) -> [pool_entry()].
build_pool(Sols) ->
  Entries = [{constraint_set:len(S), solution_variables(S), S} || S <- Sols],
  lists:sort(fun({W1, _, _}, {W2, _, _}) -> W1 =< W2 end, Entries).

%% Which variables a solution mentions: the constrained ones, plus every
%% variable occurring anywhere in a bound. Bounds repeat heavily across the
%% constraint sets of one query, and ty_node:all_variables/1 walks the node DAG
%% once and memoizes the result, so each distinct bound is walked at most once.
-spec solution_variables(solutions()) -> sets:set(variable()).
solution_variables(Sols) ->
  constraint_set:fold(
    fun(Cs, Outer) ->
      lists:foldl(
        fun({Var, Lower, Upper}, Acc) ->
          sets:union([Acc,
                      sets:from_list([Var]),
                      ty_node:all_variables(Lower),
                      ty_node:all_variables(Upper)])
        end, Outer, Cs)
    end, sets:new(), Sols).

%% The pool is kept sorted by width, so its head is always the cheapest thing to
%% merge and the walk for a partner stops at the narrowest connected entry.
-spec merge_pool([pool_entry()], monomorphic_variables()) -> boolean().
merge_pool([], _MonoVars) -> true;
merge_pool([_Single], _MonoVars) ->
  % One entry left and it is not [] -- every merge that produced it was checked
  true;
merge_pool([{_WidthA, VarsA, SolsA} | Rest], MonoVars) ->
  {{_WidthB, VarsB, SolsB}, Others} = take_partner(Rest, VarsA),
  case tally_saturate(constraint_set:meet(SolsA, SolsB, MonoVars), MonoVars) of
    [] -> false;
    Merged ->
      Entry = {constraint_set:len(Merged), sets:union(VarsA, VarsB), Merged},
      merge_pool(insert_by_width(Entry, Others), MonoVars)
  end.

%% Prefer the narrowest entry that shares a variable with the one being merged;
%% only when the rest of the pool is entirely disjoint from it is a pure
%% cartesian product unavoidable, and then the narrowest is the cheapest one.
-spec take_partner([pool_entry(), ...], sets:set(variable())) -> {pool_entry(), [pool_entry()]}.
take_partner(Pool = [Narrowest | Rest], Vars) ->
  case scan_connected(Pool, Vars, []) of
    none -> {Narrowest, Rest};
    Found -> Found
  end.

-spec scan_connected([pool_entry()], sets:set(variable()), [pool_entry()]) ->
        none | {pool_entry(), [pool_entry()]}.
scan_connected([], _Vars, _Skipped) -> none;
scan_connected([Entry = {_Width, EntryVars, _Sols} | Rest], Vars, Skipped) ->
  case sets:size(sets:intersection(Vars, EntryVars)) of
    0 -> scan_connected(Rest, Vars, [Entry | Skipped]);
    _ -> {Entry, lists:reverse(Skipped, Rest)}
  end.

%% A merged entry goes *behind* the entries it ties with, so a width class is
%% drained round-robin instead of the newest result being re-consumed
%% immediately. That is what makes the merge tree balanced rather than a chain:
%% pushing the result to the front of its class rebuilds a linear fold inside
%% the class, and that alone costs 312 ms instead of 172 ms on the query that
%% motivates v6 and 230 ms instead of 182 ms on the satisfiable one.
-spec insert_by_width(pool_entry(), [pool_entry()]) -> [pool_entry(), ...].
insert_by_width(Entry, []) -> [Entry];
insert_by_width(Entry = {Width, _, _}, Pool = [{Other, _, _} | _]) when Width < Other ->
  [Entry | Pool];
insert_by_width(Entry, [Head | Rest]) -> [Head | insert_by_width(Entry, Rest)].

% =========================
% full tally implementation

-spec tally(input_constraints()) -> {error, []} | tally_solutions().
tally(Constraints) -> tally(Constraints, #{}).

-spec tally(input_constraints(), monomorphic_variables()) -> {error, []} | tally_solutions().
tally(Constraints, MonomorphicVariables) ->
  % io:format(user,"~n~n=== Step 1: Normalize ~p constraints~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Constraints), MonomorphicVariables]),
  Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  % io:format(user,"~n~n=== Step 2: Saturate ~p sets~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Normalized), MonomorphicVariables]),
  Saturated = ?TIME(tally_saturate, tally_saturate(Normalized, MonomorphicVariables)),
  % io:format(user,"~n~n=== Step 3: Solve ~p sets~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Saturated), MonomorphicVariables]),
  Solved = ?TIME(tally_solve, tally_solve(Saturated, MonomorphicVariables)),
  % io:format(user,"~n~n=== Step 4: Solved~n~p~n===~n", [Solved]),

  % sanity: every substitution satisfies all given constraints (by polymorphic subtyping), if no error
  ?SANITY(substitutions_solve_input_constraints, case Solved of {error, _} -> ok; _ -> [ true = is_valid_substitution(Constraints, Subst, MonomorphicVariables) || Subst <- Solved] end),
 
  Solved.

-spec tally_normalize(input_constraints(), monomorphic_variables()) -> set_of_constraint_sets().
tally_normalize(Constraints, MonomorphicVariables) ->
  lists:foldl(fun
    ({_S, _T}, []) -> [];
    ({S, T}, A) ->
      SnT = ?TY:difference(S, T),
      case ty_node:normalize(SnT, MonomorphicVariables) of
        %% Short-circuit: meet(A, []) = [] — skip the meet call entirely.
        [] -> [];
        Normalized -> constraint_set:meet(A, Normalized, MonomorphicVariables)
      end
              end, [[]], Constraints).


-spec tally_saturate(set_of_constraint_sets(), monomorphic_variables()) -> set_of_constraint_sets().
tally_saturate(Normalized, MonomorphicVariables) ->
  lists:foldl(
    fun
      (_ConstraintSet, [[]]) -> [[]];
      (ConstraintSet, A) ->
        constraint_set:join(A, constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}), MonomorphicVariables) 
    end, [], Normalized).

-spec tally_solve(set_of_constraint_sets(), monomorphic_variables()) -> {error, []} | tally_solutions().
tally_solve([], _MonomorphicVariables) -> {error, []};
tally_solve(Saturated, MonomorphicVariables) ->
  Solved = solve(Saturated, MonomorphicVariables),
  [ maps:from_list(Subst) || Subst <- Solved].

-spec solve(set_of_constraint_sets(), monomorphic_variables()) -> [[{variable(), ty:type()}]].
solve(SaturatedSetOfConstraintSets, MonomorphicVariables) ->
  S = ([ solve_single(C, [], MonomorphicVariables) || C <- SaturatedSetOfConstraintSets]),
  [ unify(E) || E <- S].

-type equation() :: {eq, variable(), ty:type()}.
-spec solve_single(constraint_set(), [equation()], monomorphic_variables()) -> [equation()].
solve_single([], Equations, _) -> Equations;
solve_single([{SmallestVar, Left, Right} | Cons], Equations, Fix) ->
  % constraints are already sorted by variable ordering
  % smallest variable first
  % reuse variable
  % FreshTyVar = ty_node:make(dnf_ty_variable:singleton(ty_variable:fresh_from(SmallestVar))), 
  FreshTyVar = ty_node:make(dnf_ty_variable:singleton(SmallestVar)),

  Result = ty_node:intersect(ty_node:union(Left, FreshTyVar), Right),
  NewEq = Equations ++ [{eq, SmallestVar, Result}],

  solve_single(Cons, NewEq, Fix).

-spec unify([equation()]) -> [{variable(), ty:type()}].
unify([]) -> [];
unify(EquationList) ->
  % sort to smallest variable
  % select in E the equation α = tα for smallest α
  [Eq = {eq, Var, TA} | _Tail] = lists:usort(fun({_, Var, _}, {_, Var2, _}) -> ty_variable:leq(Var, Var2) end, EquationList),
 
  NewMap = #{Var => TA},

  E_ = 
  [ begin
      {eq, XA, ty_node:substitute(TAA, NewMap)} 
    end
        ||
    (X = {eq, XA, TAA}) <- EquationList, X /= Eq
  ],

  ?SANITY(solve_equation_list_length, true = length(EquationList) - 1 == length(E_)),

  Sigma = unify(E_),
  NewTASigma = apply_substitution(TA, Sigma),

  [{Var, NewTASigma}] ++ Sigma.


% TODO apply substitution all at once
-spec apply_substitution(ty:type(), [{variable(), ty:type()}]) -> ty:type().
apply_substitution(Ty, []) -> Ty;
apply_substitution(Ty, Substitutions) ->
  SubstFun = fun({Var, To}, Tyy) ->
    Mapping = #{Var => To},
    Result = ty_node:substitute(Tyy, Mapping),
    % since we reuse the tally variables, the same variable can appear again in the result substitution
    % only if we generate fresh variables, include this sanity check
    % ?SANITY(etally_apply_substition, sanity_substitution({Var, To}, Tyy, Result)),
    Result
             end,
  lists:foldl(SubstFun, Ty, Substitutions).

% print([]) -> "";
% print([X | Xs]) when is_list(X) -> 
%   io_lib:format(">>~n~s~n~s", [print(X), print(Xs)]);
% print([{{var, name, Name}, Left, Right} | Rest]) -> 
%   io_lib:format("~s <: ~p <: ~s~n~s", [pretty:render_ty(ty_parser:unparse(Left)), Name, pretty:render_ty(ty_parser:unparse(Right)), print(Rest)]);
% print([{Left, Right} | Rest]) -> 
%   io_lib:format("~s <: ~s~n~s", [pretty:render_ty(ty_parser:unparse(Left)), pretty:render_ty(ty_parser:unparse(Right)), print(Rest)]).
