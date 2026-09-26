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
%     P -> R <: A -> B      ==  A <: P, R <: B                  if A is non-empty
%     #{K1 => V1} <: #{K2 => V2}  ==  K1 <: K2, V1 <: V2        if K1 and V1 are non-empty
%
% A map type with an empty key or value domain contains the empty map only, and
% the empty map is in every map type, so like a list the map rule needs its left
% side non-empty in both positions. Every map type is itself non-empty.
%
% The arrow rule is the one the peel needs most: a lambda passed to a polymorphic
% higher-order function (a fold, a map) is constrained by `fun(Params) -> Body <:
% fun(T, Acc) -> Acc`, which holds every variable of the lambda at both polarities
% at once. Decomposed, its parameters become plain lower bounds and its body a
% plain upper bound. With several arguments the domain is their tuple, so every
% argument has to be non-empty.
%
%     S <: {T1, .., Tn}     ==  pi_1(S) <: T1, .., pi_n(S) <: Tn  for a ground S made of n-tuples
%     S <: [H @ R]          ==  pi_hd(S) <: H, pi_tl(S) <: R      for a ground S made of cons cells
%
% The projection rule is where a pattern binds its variables. `case E of {tag, X, Y}
% -> ..` constrains the scrutinee's type against `{$tag, $X, $Y}`, and the left side
% is that type met with the pattern's shape, less the patterns of the clauses
% before: typically a named AST type, a tuple of any()s, and negated tuple
% patterns. Written as a union of non-empty n-tuples, S <: {T1..Tn} holds exactly
% when the union of the i-th components is below Ti for every i, so each pattern
% variable gets the projection of the scrutinee as a bare lower bound.
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
                none -> projected(C, {tuple, length(Ts)}, Ts, SymTab)
            end;
        {{fun_full, Ps, R}, {fun_full, As, B}} when length(Ps) =:= length(As) ->
            if_nonempty(As, lists:zip(As, Ps) ++ [{R, B}], C, LBs, SymTab);
        {{map, [{map_field_opt, K1, V1}]}, {map, [{map_field_opt, K2, V2}]}} ->
            if_nonempty([K1, V1], [{K1, K2}, {V1, V2}], C, LBs, SymTab);
        {{list, A}, {list, B}} -> if_nonempty([A], [{A, B}], C, LBs, SymTab);
        {{nonempty_list, A}, {list, B}} -> if_nonempty([A], [{A, B}], C, LBs, SymTab);
        {{nonempty_list, A}, {nonempty_list, B}} -> if_nonempty([A], [{A, B}], C, LBs, SymTab);
        {{cons, H, R}, {list, B}} -> if_nonempty([H, R], [{H, B}, {R, {list, B}}], C, LBs, SymTab);
        {{cons, H, R}, {nonempty_list, B}} -> if_nonempty([H, R], [{H, B}, {R, {list, B}}], C, LBs, SymTab);
        {{cons, H1, R1}, {cons, H2, R2}} -> if_nonempty([H1, R1], [{H1, H2}, {R1, R2}], C, LBs, SymTab);
        {_, {tuple, Ts}} -> projected(C, {tuple, length(Ts)}, Ts, SymTab);
        {_, {cons, H, R}} -> projected(C, cons, [H, R], SymTab);
        _ -> [C]
    end.

% The projection rule; only worth trying when the right side has variables to bound.
% shape: {tuple, N} for n-tuples, cons for cons cells (head and tail)
-type shape() :: {tuple, pos_integer()} | cons.

-spec projected({ast:ty(), ast:ty()}, shape(), [ast:ty()], symtab:t()) -> constraints().
projected(C = {S, _}, Shape, Ts, SymTab) ->
    case lists:any(fun(Ti) -> not sets:is_empty(tyutils:free_in_ty(Ti)) end, Ts)
         andalso sets:is_empty(tyutils:free_in_ty(S)) of
        true ->
            case project(S, Shape, SymTab) of
                {ok, Pis} -> lists:zip(Pis, Ts);
                none -> [C]
            end;
        false -> [C]
    end.

-spec arity(shape()) -> pos_integer().
arity({tuple, N}) -> N;
arity(cons) -> 2.

-spec any_of(shape()) -> ast:ty().
any_of({tuple, N}) -> {tuple, lists:duplicate(N, {predef, any})};
any_of(cons) -> {cons, {predef, any}, {predef, any}}.

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
nonempty({map, Assocs}, LBs, SymTab, D) ->
    % the empty map is in every map type whose required associations can be met
    lists:all(fun({map_field_opt, _, _}) -> true;
                 ({map_field_req, K, V}) -> nonempty(K, LBs, SymTab, D) andalso nonempty(V, LBs, SymTab, D)
              end, Assocs);
nonempty({predef, none}, _, _, _) -> false;
nonempty({predef, _}, _, _, _) -> true;
nonempty({predef_alias, _}, _, _, _) -> true;
nonempty(T, _LBs, SymTab, _) -> nonempty_ground(T, SymTab).

% A ground type is non-empty when it is not a subtype of none().
-spec nonempty_ground(ast:ty(), symtab:t()) -> boolean().
nonempty_ground(T, SymTab) ->
    case sets:is_empty(tyutils:free_in_ty(T)) of
        true -> not subty(SymTab, T, {predef, none});
        false -> false
    end.

% The semantic questions asked here are about ground types, mostly the AST types
% of a module and their components, and the same ones come up in every check of
% every function. The answers are kept per process for as long as the type
% definitions of the symtab do not change.
-spec subty(symtab:t(), ast:ty(), ast:ty()) -> boolean().
subty(SymTab, S, T) ->
    memo(SymTab, {subty, S, T}, fun() -> subty:is_subty(SymTab, S, T) end).

-spec memo(symtab:t(), term(), fun(() -> R)) -> R.
memo(SymTab, Key, Compute) ->
    Types = symtab:get_types(SymTab),
    Cache = case erlang:get(decompose_cache) of
        {Types, C} -> C;
        _ -> #{}
    end,
    case Cache of
        #{Key := R} -> R;
        _ ->
            R = Compute(),
            erlang:put(decompose_cache, {Types, Cache#{Key => R}}),
            R
    end.

% pi_1(S) .. pi_n(S) for a ground S that is an intersection containing an
% n-tuple, made of tuples, unions of tuples, named types unfolding to those, and
% negations of tuple patterns. A member contained in a negated pattern vanishes,
% one disjoint from it stays, a partial overlap gives up. Empty members are
% dropped, which is what makes the result exact.
-spec project(ast:ty(), shape(), symtab:t()) -> {ok, [ast:ty()]} | none.
project(S, Shape, SymTab) ->
    memo(SymTab, {project, S, Shape}, fun() ->
        case members(S, Shape, SymTab, 4) of
            none -> none;
            {ok, Members} ->
                NonEmpty = [M || M <- Members, lists:all(fun(X) -> nonempty_ground(X, SymTab) end, M)],
                Cols = lists:foldl(
                    fun(M, Acc) -> [[X | Col] || {X, Col} <- lists:zip(M, Acc)] end,
                    lists:duplicate(arity(Shape), []), NonEmpty),
                {ok, [ast_lib:mk_union(lists:usort(Col)) || Col <- Cols]}
        end
    end).

% The n-tuples whose union is S /\ {any()^n}, as component lists. S has to be an
% intersection with an n-tuple among its members, so that S is made of n-tuples.
-spec members(ast:ty(), shape(), symtab:t(), non_neg_integer()) -> {ok, [[ast:ty()]]} | none.
members({intersection, Ss}, Shape, SymTab, D) ->
    case lists:any(fun(X) -> literal_of_shape(X, Shape) end, Ss) of
        false -> none;
        true ->
            Pos = [X || X <- Ss, element(1, X) =/= negation],
            Neg = [X || {negation, X} <- Ss],
            case pos_members(Pos, Shape, SymTab, D) of
                none -> none;
                {ok, Ms} -> apply_negs(Ms, Neg, Shape, SymTab)
            end
    end;
members(_, _, _, _) -> none.

% S has to be made of values of the shape, which a literal member guarantees
-spec literal_of_shape(ast:ty(), shape()) -> boolean().
literal_of_shape({tuple, Cs}, {tuple, N}) -> length(Cs) =:= N;
literal_of_shape({cons, _, _}, cons) -> true;
literal_of_shape({nonempty_list, _}, cons) -> true;
literal_of_shape(_, _) -> false.

% the cartesian meet of the positive members' tuples
-spec pos_members([ast:ty()], shape(), symtab:t(), non_neg_integer()) -> {ok, [[ast:ty()]]} | none.
pos_members(Pos, Shape, SymTab, D) ->
    lists:foldl(
        fun(_, none) -> none;
           (P, {ok, Acc}) ->
                case shape_members(P, Shape, SymTab, D) of
                    none -> none;
                    {ok, Ms} -> {ok, [[ast_lib:mk_intersection([A, B]) || {A, B} <- lists:zip(M1, M2)] || M1 <- Acc, M2 <- Ms]}
                end
        end, {ok, [lists:duplicate(arity(Shape), {predef, any})]}, Pos).

% the values of the shape in one positive member, as component lists; named
% types are unfolded up to depth D
-spec shape_members(ast:ty(), shape(), symtab:t(), non_neg_integer()) -> {ok, [[ast:ty()]]} | none.
shape_members({tuple, Cs}, {tuple, N}, _, _) when length(Cs) =:= N -> {ok, [Cs]};
shape_members({tuple, _}, _, _, _) -> {ok, []};
shape_members({tuple_any}, {tuple, N}, _, _) -> {ok, [lists:duplicate(N, {predef, any})]};
shape_members({tuple_any}, cons, _, _) -> {ok, []};
shape_members({cons, H, R}, cons, _, _) -> {ok, [[H, R]]};
shape_members({nonempty_list, A}, cons, _, _) -> {ok, [[A, {list, A}]]};
shape_members({list, A}, cons, _, _) -> {ok, [[A, {list, A}]]};   % the [] part holds no cons cell
shape_members({cons, _, _}, {tuple, _}, _, _) -> {ok, []};
shape_members({nonempty_list, _}, {tuple, _}, _, _) -> {ok, []};
shape_members({list, _}, {tuple, _}, _, _) -> {ok, []};
shape_members({empty_list}, _, _, _) -> {ok, []};
shape_members({predef, any}, Shape, _, _) -> {ok, [lists:duplicate(arity(Shape), {predef, any})]};
shape_members({union, Us}, Shape, SymTab, D) ->
    lists:foldl(
        fun(_, none) -> none;
           (U, {ok, Acc}) ->
                case shape_members(U, Shape, SymTab, D) of none -> none; {ok, Ms} -> {ok, Acc ++ Ms} end
        end, {ok, []}, Us);
shape_members({named, Loc, Ref, Args}, Shape, SymTab, D) when D > 0 ->
    try
        {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, Loc, SymTab),
        Unfolded = subst:apply(subst:from_list(lists:zip([V || {V, _} <- Vars], Args)), Body, no_clean),
        shape_members(Unfolded, Shape, SymTab, D - 1)
    catch _:_ -> none
    end;
shape_members(I = {intersection, _}, Shape, SymTab, D) -> members(I, Shape, SymTab, D);
shape_members(T, Shape, SymTab, _) -> ground_members(T, Shape, SymTab).

% A ground type of any other syntax either misses the values of the shape
% A ground type of any other syntax either misses the values of the shape
% entirely, or contains all of them, or is left alone.
-spec ground_members(ast:ty(), shape(), symtab:t()) -> {ok, [[ast:ty()]]} | none.
ground_members(T, Shape, SymTab) ->
    case sets:is_empty(tyutils:free_in_ty(T)) of
        false -> none;
        true ->
            Any = any_of(Shape),
            case subty(SymTab, ast_lib:mk_intersection([T, Any]), {predef, none}) of
                true -> {ok, []};
                false ->
                    case subty(SymTab, Any, T) of
                        true -> {ok, [lists:duplicate(arity(Shape), {predef, any})]};
                        false -> none
                    end
            end
    end.

% subtract the negated patterns, member by member
-spec apply_negs([[ast:ty()]], [ast:ty()], shape(), symtab:t()) -> {ok, [[ast:ty()]]} | none.
apply_negs(Ms, [], _Shape, _SymTab) -> {ok, Ms};
apply_negs(Ms, [Neg | Negs], Shape, SymTab) ->
    Pats = case neg_patterns(Neg, Shape) of none -> ground_members(Neg, Shape, SymTab); R -> R end,
    case Pats of
        none -> none;
        {ok, Ps} ->
            case subtract_all(Ms, Ps, SymTab) of
                none -> none;
                {ok, Ms2} -> apply_negs(Ms2, Negs, Shape, SymTab)
            end
    end.

% the patterns of the shape inside a negated type; values of other shapes do not
% touch the shape
-spec neg_patterns(ast:ty(), shape()) -> {ok, [[ast:ty()]]} | none.
neg_patterns({tuple, Cs}, {tuple, N}) when length(Cs) =:= N -> {ok, [Cs]};
neg_patterns({tuple, _}, _) -> {ok, []};
neg_patterns({cons, H, R}, cons) -> {ok, [[H, R]]};
neg_patterns({nonempty_list, A}, cons) -> {ok, [[A, {list, A}]]};
neg_patterns({list, A}, cons) -> {ok, [[A, {list, A}]]};
neg_patterns({cons, _, _}, _) -> {ok, []};
neg_patterns({nonempty_list, _}, _) -> {ok, []};
neg_patterns({list, _}, _) -> {ok, []};
neg_patterns({union, Us}, Shape) ->
    lists:foldl(fun(_, none) -> none;
                   (U, {ok, Acc}) -> case neg_patterns(U, Shape) of none -> none; {ok, Ps} -> {ok, Acc ++ Ps} end
                end, {ok, []}, Us);
neg_patterns({intersection, [X]}, Shape) -> neg_patterns(X, Shape);
neg_patterns({intersection, Xs}, Shape) ->
    % {..} /\ {any(), ..}: the componentwise meet of the members' patterns
    Rs = [neg_patterns(X, Shape) || X <- Xs],
    case lists:all(fun({ok, [_]}) -> true; (_) -> false end, Rs) of
        true -> {ok, [[ast_lib:mk_intersection(Col) || Col <- transpose([P || {ok, [P]} <- Rs])]]};
        false -> none
    end;
neg_patterns({singleton, _}, _) -> {ok, []};
neg_patterns({empty_list}, _) -> {ok, []};
neg_patterns({fun_full, _, _}, _) -> {ok, []};
neg_patterns({range, _, _}, _) -> {ok, []};
neg_patterns({map_any}, _) -> {ok, []};
neg_patterns({map, _}, _) -> {ok, []};
neg_patterns({predef, none}, _) -> {ok, []};
neg_patterns(_, _) -> none.

-spec transpose([[ast:ty()]]) -> [[ast:ty()]].
transpose([]) -> [];
transpose([[] | _]) -> [];
transpose(Rows) -> [[hd(R) || R <- Rows] | transpose([tl(R) || R <- Rows])].

% a member disjoint from the pattern in some component stays, one contained in
% every component vanishes; anything in between is not representable here
-spec subtract_all([[ast:ty()]], [[ast:ty()]], symtab:t()) -> {ok, [[ast:ty()]]} | none.
subtract_all(Ms, [], _SymTab) -> {ok, Ms};
subtract_all(Ms, [P | Ps], SymTab) ->
    R = lists:foldl(
        fun(_, none) -> none;
           (M, {ok, Acc}) ->
                Disjoint = lists:any(fun({A, B}) -> subty(SymTab, ast_lib:mk_intersection([A, B]), {predef, none}) end, lists:zip(M, P)),
                case Disjoint of
                    true -> {ok, [M | Acc]};
                    false ->
                        case lists:all(fun({A, B}) -> subty(SymTab, A, B) end, lists:zip(M, P)) of
                            true -> {ok, Acc};
                            false -> none
                        end
                end
        end, {ok, []}, Ms),
    case R of none -> none; {ok, Ms2} -> subtract_all(lists:reverse(Ms2), Ps, SymTab) end.

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
        % arrows: the arguments of the expected type bound the parameters, the
        % body the result; an argument variable needs a non-empty lower bound
        Lam = {fun_full, [A, B], {tuple, [A, B]}},
        Expected = {fun_full, [Int, V], V},
        [{Int, A}, {V, B}, {{tuple, [A, B]}, V}] = Step([{Lam, Expected}, {Atom, V}]) -- [{Atom, V}],
        StuckArrow = [{Lam, Expected}],
        StuckArrow = Step(StuckArrow),
        % projection: the union of tuples on the left, less the negated pattern,
        % bounds each pattern variable by its component
        Scrut = {intersection, [{union, [{tuple, [{singleton, a}, Int]}, {tuple, [{singleton, b}, Atom]}]},
                                {tuple, [{predef, any}, {predef, any}]},
                                {negation, {tuple, [{singleton, a}, {predef, any}]}}]},
        [{{singleton, b}, {predef, any}}, {Atom, A}] = Step([{Scrut, {tuple, [{predef, any}, A]}}]),
        % a variable on the left, or no variable on the right: untouched
        Var = [{{intersection, [V, {tuple, [{predef, any}]}]}, {tuple, [A]}}],
        Var = Step(Var),
        Ground = [{Scrut, {tuple, [{predef, any}, Atom]}}],
        Ground = Step(Ground),
        % maps: an empty key or value domain would leave the empty map only
        Map = fun(K, Val) -> {map, [{map_field_opt, K, Val}]} end,
        [{Int, A}, {Atom, B}] = Step([{Map(Int, Atom), Map(A, B)}]),
        StuckMap = [{Map(V, Atom), Map(A, B)}],
        StuckMap = Step(StuckMap),
        [{Int, V}, {V, A}, {Atom, B}] = Step([{Int, V} | StuckMap]),
        % cons projection: a ground list pattern binds head and tail
        L3 = {intersection, [{cons, Atom, {cons, Int, {empty_list}}}, {cons, {predef, any}, {predef, any}}]},
        [{Atom, A}, {{cons, Int, {empty_list}}, B}] = Step([{L3, {cons, A, B}}]),
        % lists and conses
        [{Int, A}] = Step([{{list, Int}, {list, A}}]),
        [{Int, A}, {{empty_list}, {list, A}}] = Step([{{cons, Int, {empty_list}}, {list, A}}]),
        ok
    end).

-endif.
