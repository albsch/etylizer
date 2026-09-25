-module(decompose).

% Takes a structural subtype constraint apart into the constraints on its
% components, exactly: every rule replaces a constraint by constraints that hold
% under precisely the same assignments of the type variables. The peel in
% subst:clean_cons cannot look through a tuple, a list or an arrow, so a bound
% hidden in such a constraint keeps its variable alive, at both polarities more
% often than not, and keeps tally's partitions in one piece.
%
%     S1 | S2 <: T          ==  S1 <: T, S2 <: T
%     S <: T1 /\ T2         ==  S <: T1, S <: T2
%     {S1, .., Sn} <: {T1, .., Tn}  ==  S1 <: T1, .., Sn <: Tn   if every Si is non-empty
%     list(A) <: list(B)    ==  A <: B                          if A is non-empty
%     [H @ R] <: list(B)    ==  H <: B, R <: list(B)            if H and R are non-empty
%
% The side conditions are what makes the tuple and list rules exact:
% {S1, S2} <: {T1, T2} also holds when S1 or S2 is empty, whatever T1 and T2 are.
% Non-emptiness has to hold under every assignment: a ground type is decided
% semantically, a variable through a non-empty ground lower bound.

-export([step/3]).

-export_type([constraints/0]).

-type constraints() :: [{ast:ty(), ast:ty()}].
-type lower_bounds() :: #{ast:ty_varname() => [ast:ty()]}.

% One pass over the constraints. Callers iterate it with the peel.
-spec step(constraints(), sets:set(ast:ty_varname()), symtab:t()) -> constraints().
step(Cons, Fixed, SymTab) ->
    LBs = lower_bounds(Cons, Fixed),
    lists:flatmap(fun(C) -> rule(C, LBs, SymTab) end, Cons).

% The bare lower bounds `L <: V` of the non-fixed variables.
-spec lower_bounds(constraints(), sets:set(ast:ty_varname())) -> lower_bounds().
lower_bounds(Cons, Fixed) ->
    lists:foldl(
        fun({L, {var, V}}, Acc) when is_atom(V) ->
                case sets:is_element(V, Fixed) of
                    true -> Acc;
                    false -> maps:update_with(V, fun(Ls) -> [L | Ls] end, [L], Acc)
                end;
           (_, Acc) -> Acc
        end, #{}, Cons).

-spec rule({ast:ty(), ast:ty()}, lower_bounds(), symtab:t()) -> constraints().
rule(C = {S, T}, LBs, SymTab) ->
    case {S, T} of
        {_, {intersection, Ts}} -> [{S, Ti} || Ti <- Ts];
        {{union, Ss}, _} -> [{Si, T} || Si <- Ss];
        {{tuple, Ss}, {tuple, Ts}} when length(Ss) =:= length(Ts) ->
            if_nonempty(Ss, lists:zip(Ss, Ts), C, LBs, SymTab);
        {{intersection, Ss}, {tuple, Ts}} ->
            case tuple_meet(Ss, length(Ts)) of
                {ok, Ms} -> if_nonempty(Ms, lists:zip(Ms, Ts), C, LBs, SymTab);
                none -> [C]
            end;
        {{list, A}, {list, B}} -> if_nonempty([A], [{A, B}], C, LBs, SymTab);
        {{nonempty_list, A}, {list, B}} -> if_nonempty([A], [{A, B}], C, LBs, SymTab);
        {{nonempty_list, A}, {nonempty_list, B}} -> if_nonempty([A], [{A, B}], C, LBs, SymTab);
        {{cons, H, R}, {list, B}} -> if_nonempty([H, R], [{H, B}, {R, {list, B}}], C, LBs, SymTab);
        {{cons, H, R}, {nonempty_list, B}} -> if_nonempty([H, R], [{H, B}, {R, {list, B}}], C, LBs, SymTab);
        {{cons, H1, R1}, {cons, H2, R2}} -> if_nonempty([H1, R1], [{H1, H2}, {R1, R2}], C, LBs, SymTab);
        _ -> [C]
    end.

-spec if_nonempty([ast:ty()], constraints(), {ast:ty(), ast:ty()}, lower_bounds(), symtab:t()) -> constraints().
if_nonempty(Conditions, Decomposed, Original, LBs, SymTab) ->
    case lists:all(fun(X) -> nonempty(X, LBs, SymTab) end, Conditions) of
        true -> Decomposed;
        false -> [Original]
    end.

% The componentwise meet of an intersection of n-tuples (any() members are dropped).
-spec tuple_meet([ast:ty()], non_neg_integer()) -> {ok, [ast:ty()]} | none.
tuple_meet(Ss, N) ->
    Tuples = [Cs || {tuple, Cs} <- Ss],
    case length(Tuples) =:= length([S || S <- Ss, S =/= {predef, any}, S =/= {tuple_any}])
         andalso Tuples =/= []
         andalso lists:all(fun(Cs) -> length(Cs) =:= N end, Tuples) of
        false -> none;
        true ->
            Cols = lists:foldl(
                fun(Cs, Acc) -> [[C | Col] || {C, Col} <- lists:zip(Cs, Acc)] end,
                lists:duplicate(N, []), Tuples),
            {ok, [ast_lib:mk_intersection(lists:reverse(Col)) || Col <- Cols]}
    end.

% Non-empty under every assignment of the variables. A variable qualifies
% through a lower bound that does; the depth bound cuts cycles such as
% `A <: B, B <: A`.
-spec nonempty(ast:ty(), lower_bounds(), symtab:t()) -> boolean().
nonempty(T, LBs, SymTab) -> nonempty(T, LBs, SymTab, 3).

-spec nonempty(ast:ty(), lower_bounds(), symtab:t(), non_neg_integer()) -> boolean().
nonempty(_, _, _, 0) -> false;
nonempty({var, V}, LBs, SymTab, D) ->
    lists:any(fun(L) -> nonempty(L, LBs, SymTab, D - 1) end, maps:get(V, LBs, []));
nonempty({tuple, Cs}, LBs, SymTab, D) -> lists:all(fun(X) -> nonempty(X, LBs, SymTab, D) end, Cs);
nonempty({cons, H, R}, LBs, SymTab, D) -> nonempty(H, LBs, SymTab, D) andalso nonempty(R, LBs, SymTab, D);
nonempty({union, Us}, LBs, SymTab, D) -> lists:any(fun(X) -> nonempty(X, LBs, SymTab, D) end, Us);
nonempty({intersection, Ts}, LBs, SymTab, D) ->
    % [H1 @ R1] /\ [H2 @ R2] is [H1 /\ H2 @ R1 /\ R2]
    Conses = [C || C = {cons, _, _} <- Ts],
    case length(Conses) =:= length([T || T <- Ts, T =/= {predef, any}]) andalso Conses =/= [] of
        true -> nonempty({cons, ast_lib:mk_intersection([H || {cons, H, _} <- Conses]),
                               ast_lib:mk_intersection([R || {cons, _, R} <- Conses])}, LBs, SymTab, D);
        false -> nonempty_ground({intersection, Ts}, SymTab)
    end;
nonempty({list, _}, _, _, _) -> true;       % contains []
nonempty({empty_list}, _, _, _) -> true;
nonempty({singleton, _}, _, _, _) -> true;
nonempty({range, _, _}, _, _, _) -> true;
nonempty({fun_full, _, _}, _, _, _) -> true;
nonempty({fun_any_arg, _}, _, _, _) -> true;
nonempty({fun_simple}, _, _, _) -> true;
nonempty({tuple_any}, _, _, _) -> true;
nonempty({map_any}, _, _, _) -> true;
nonempty({predef, none}, _, _, _) -> false;
nonempty({predef, _}, _, _, _) -> true;
nonempty({predef_alias, _}, _, _, _) -> true;
nonempty(T, _LBs, SymTab, _) -> nonempty_ground(T, SymTab).

% A ground type is non-empty when it is not a subtype of none(). The same ground
% types (the AST types of a module, mostly) come up in every check of every
% function, so the answers are kept per process for as long as the type
% definitions of the symtab do not change.
-spec nonempty_ground(ast:ty(), symtab:t()) -> boolean().
nonempty_ground(T, SymTab) ->
    case sets:is_empty(tyutils:free_in_ty(T)) of
        true ->
            Types = symtab:get_types(SymTab),
            Cache = case erlang:get(decompose_nonempty_cache) of
                {Types, C} -> C;
                _ -> #{}
            end,
            case Cache of
                #{T := R} -> R;
                _ ->
                    R = not subty:is_subty(SymTab, T, {predef, none}),
                    erlang:put(decompose_nonempty_cache, {Types, Cache#{T => R}}),
                    R
            end;
        false -> false
    end.

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

step_test() ->
    global_state:with_new_state(fun() ->
        A = {var, 'A'}, B = {var, 'B'}, V = {var, 'V'},
        Int = stdtypes:tint(), Atom = stdtypes:tatom(),
        Step = fun(Cs) -> step(Cs, sets:new(), symtab:empty()) end,
        % splits need no side condition
        [{Int, A}, {Atom, A}] = Step([{{union, [Int, Atom]}, A}]),
        [{A, Int}, {A, Atom}] = Step([{A, {intersection, [Int, Atom]}}]),
        % ground components are non-empty: componentwise
        [{Int, A}, {Atom, B}] = Step([{{tuple, [Int, Atom]}, {tuple, [A, B]}}]),
        % a variable component needs a non-empty lower bound
        Stuck = [{{tuple, [V, Atom]}, {tuple, [A, B]}}],
        Stuck = Step(Stuck),
        [{Int, V}, {V, A}, {Atom, B}] = Step([{Int, V} | Stuck]),
        % an empty component keeps the constraint whole
        Empty = [{{tuple, [{predef, none}, Atom]}, {tuple, [A, B]}}],
        Empty = Step(Empty),
        % intersections of tuples are met componentwise first
        [{Int, A}] = Step([{{intersection, [{tuple, [Int]}, {tuple, [{predef, any}]}]}, {tuple, [A]}}]),
        % lists and conses
        [{Int, A}] = Step([{{list, Int}, {list, A}}]),
        [{Int, A}, {{empty_list}, {list, A}}] = Step([{{cons, Int, {empty_list}}, {list, A}}]),
        ok
    end).

-endif.
