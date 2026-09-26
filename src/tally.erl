-module(tally).

-export([
  tally/2,
  tally/3,
  is_satisfiable/3
]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-import(stdtypes, [tvar/1]).
-endif.

-include("metrics.hrl").

-export_type([monomorphic_variables/0]).

-ifdef(ety_metrics).
var_metrics(FixedVars, Constraints, _SymTab) ->
    {_NC, Poly, Frame, MonoUsed, MonoUnused} = shape_metrics(Constraints, FixedVars),
    {current_fn(), Poly, Frame, MonoUsed, MonoUnused}.

%% Compute {NumConstraints, Poly, Frame, MonoUsed, MonoUnused} for a list of
%% constraints. Poly = non-fixed vars whose atom name does not start with "%";
%% Frame = non-fixed vars whose name starts with "%" (gradual framevars).
shape_metrics(Constraints, FixedVars) ->
    NumConstrs = length(Constraints),
    AllVars = sets:from_list(utils:everything(
        fun({var, V}) when is_atom(V) -> {ok, V}; (_) -> error end, Constraints)),
    MonoUsed = sets:size(sets:intersection(AllVars, FixedVars)),
    MonoUnused = sets:size(FixedVars) - MonoUsed,
    NonFixed = sets:subtract(AllVars, FixedVars),
    {Poly, Frame} = sets:fold(
        fun(V, {P, F}) ->
            case atom_to_list(V) of
                [$% | _] -> {P, F + 1};
                _        -> {P + 1, F}
            end
        end, {0, 0}, NonFixed),
    {NumConstrs, Poly, Frame, MonoUsed, MonoUnused}.

current_fn() ->
    case ?METRIC_GET_FUN() of undefined -> '__no_fun__'; X -> X end.

record_tally_invocation(NumPartitions) ->
    metrics:record(tally_invocation, {current_fn(), NumPartitions}).

%% Shape is recorded for every partition (cheap, unbiased by early-exit).
record_partition_shapes(Partitions, FixedVars) ->
    lists:foreach(
      fun(P) ->
          {NC, Po, Fr, MU, MX} = shape_metrics(P, FixedVars),
          metrics:record(tally_partition, {current_fn(), NC, Po, Fr, MU, MX})
      end, Partitions).

-endif.

-type monomorphic_variables() :: sets:set(ast:ty_varname()).
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).
-type constraints_partition() :: #{term() => [{ast:ty(), ast:ty()}]}.

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, Constraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs0, _SubtyConstrs, _Maters, _UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),
    InlinedConstrs = resolve_overloads(SymTab, InlinedConstrs0),

    % Deterministic sort: primary by erts_debug:size, secondary by full term so
    % size ties don't leak the sets:to_list order into
    % the constraint sequence consumed by the algorithm.
    InternalRawConstraints =
    [{S, T} ||
        {_Size, {scsubty, _, S, T}} <-
            lists:sort(
                [{erts_debug:size({S, T}), C}
                 || C = {scsubty, _, S, T} <- sets:to_list(InlinedConstrs)])],

    % cleaning is OK, we only care about one solution
    FinalCons = clean(InternalRawConstraints, FixedVars, SymTab),

    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),
    ?METRIC(poly_vars, var_metrics(FixedVars, FinalCons, SymTab)),

    % Split constraints into independent partitions
    MM = split(FinalCons, FixedVars),
    % Sort partitions by key for deterministic processing order
    Partitions = [V || {_, V} <- lists:sort(maps:to_list(MM))],
    ?METRIC_DO(record_tally_invocation(length(Partitions))),
    ?METRIC_DO(record_partition_shapes(Partitions, FixedVars)),
    case Partitions of
        [] -> {true, satisfiable}; % no subtype constraints
        [First | Rest] ->
            % Check satisfiability for each partition
            FirstRes = do_satisfiable(First, MonomorphicTallyVariables),
            lists:foldl(fun(_, {false, _}) -> {false, []};
                           (C, {true, _}) -> do_satisfiable(C, MonomorphicTallyVariables)
                        end, FirstRes, Rest)
    end.

% The peel of subst:clean_cons removes a variable once it has a bare bound, but
% a bound hidden inside a tuple, a list or an arrow is invisible to it, and the
% variable then looks nested at both polarities. decompose:step takes such
% constraints apart, exactly; the peel removes the variables that exposes,
% which makes further constraints decomposable, until a round changes nothing.
% Overload resolution runs again in every round, because a peel can turn an
% argument type concrete. Termination: a round either removes a variable for
% good or replaces a constraint by constraints on its components.
-spec clean([{ast:ty(), ast:ty()}], monomorphic_variables(), symtab:t()) -> [{ast:ty(), ast:ty()}].
clean(Cons, FixedVars, SymTab) ->
    rounds(subst:clean_cons(Cons, FixedVars, SymTab), FixedVars, SymTab).

-spec rounds([{ast:ty(), ast:ty()}], monomorphic_variables(), symtab:t()) -> [{ast:ty(), ast:ty()}].
rounds(Cons, FixedVars, SymTab) ->
    Resolved = lists:flatmap(
        fun({S, T}) ->
            [{S2, T2} || {scsubty, _, S2, T2} <- resolve_overload(SymTab, {scsubty, ast:loc_auto(), S, T})]
        end, Cons),
    Decomposed = decompose:step(Resolved, FixedVars, SymTab),
    case lists:usort(Decomposed) =:= lists:usort(Cons) of
        true -> Cons;
        false -> rounds(subst:peel_cons(Decomposed, FixedVars, SymTab), FixedVars, SymTab)
    end.

-spec do_satisfiable([{ast:ty(), ast:ty()}], map()) ->
    {false, [{error, string()}]} | {true, term()}.
do_satisfiable(FinalCons, MonomorphicTallyVariables) ->
    ?METRIC_DO(T0 = erlang:monotonic_time(microsecond)),
    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- FinalCons],
    InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),
    ?METRIC_DO(metrics:record(tally_partition_time, {current_fn(), erlang:monotonic_time(microsecond) - T0})),
    case InternalResult of
        false -> {false, []};
        true -> {true, satisfiable}
    end.

% Overload resolution before tally. For a constraint F <= (A1,...,An) -> B where F is an
% intersection of arrows, a clause whose parameters are disjoint from the argument
% types A1,...,An cannot apply. If exactly one clause (P1,...,Pn) -> R remains, the
% constraint is replaced by A1 <= P1, ..., An <= Pn and R <= B. This spares tally the
% normalization of the intersection of arrows, which is exponential in the clauses.
% Type variables overlap with everything, so they can only prevent the replacement.
-spec resolve_overloads(symtab:t(), constr:subty_constrs()) -> constr:subty_constrs().
resolve_overloads(SymTab, Constrs) ->
    sets:from_list(lists:flatmap(fun(C) -> resolve_overload(SymTab, C) end, sets:to_list(Constrs))).


-spec resolve_overload(symtab:t(), constr:simp_constr_subty()) -> [constr:simp_constr_subty()].
resolve_overload(SymTab, C = {scsubty, Loc, {intersection, FunTys}, {fun_full, ArgTys, ResTy}}) ->
    IsClause = fun({fun_full, ParamTys, _}) -> length(ParamTys) =:= length(ArgTys); (_) -> false end,
    case lists:all(IsClause, FunTys) of
        false -> [C];
        true ->
            case [F || F = {fun_full, ParamTys, _} <- FunTys, overlaps(SymTab, ArgTys, ParamTys)] of
                [{fun_full, ParamTys, ClauseResTy}] ->
                    [{scsubty, Loc, ClauseResTy, ResTy} |
                     [{scsubty, Loc, A, P} || {A, P} <- lists:zip(ArgTys, ParamTys)]];
                Overlapping ->
                    case top_of_chain(SymTab, Overlapping, ArgTys) of
                        {ok, Top} -> [{scsubty, Loc, Top, {fun_full, ArgTys, ResTy}}];
                        none -> [C]
                    end
            end
    end;
resolve_overload(_SymTab, C) -> [C].

% A refinement chain of clauses, P1 -> R1 with P1 <: P2 and R1 <: R2 and so on
% (lists:usort: (nonempty_list(T)) -> nonempty_list(T); (list(T)) -> list(T)),
% applied to an argument that surely holds a value outside every clause but the
% last (here []): the intersection then applies exactly like its last clause. A value of the argument at level i gets the result R_i, and R_i <: R_n,
% so once level n is hit, R_n <: B is required and implies the others, while
% A <: P_n is required anyway. Type variables of the spec are opaque in the chain
% test; the smallest instance of the argument is compared against the largest
% instance of P_{n-1}, so the witness exists under every assignment.
-spec top_of_chain(symtab:t(), [ast:ty()], [ast:ty()]) -> {ok, ast:ty()} | none.
top_of_chain(_SymTab, Clauses, _ArgTys) when length(Clauses) < 2 -> none; % nothing to drop
top_of_chain(SymTab, Clauses, ArgTys) ->
    % the witness has to exist for every instance of the argument: look for it
    % in the smallest one (variables at covariant positions none(), at
    % contravariant positions any()), which is below every instance
    case smallest_instance({tuple, ArgTys}, 0) of
        none -> none;
        {ok, Smallest} ->
            Refines = fun({fun_full, P1, R1}, {fun_full, P2, R2}) ->
                subty:is_subty(SymTab, {tuple, P1}, {tuple, P2}) andalso subty:is_subty(SymTab, R1, R2)
            end,
            Chain = lists:all(fun({F1, F2}) -> Refines(F1, F2) end,
                              lists:zip(lists:droplast(Clauses), tl(Clauses))),
            case Chain of
                false -> none;
                true ->
                    Top = {fun_full, _, _} = lists:last(Clauses),
                    {fun_full, PBelow, _} = lists:last(lists:droplast(Clauses)),
                    Largest = utils:everywhere(fun({var, V}) when is_atom(V) -> {ok, {predef, any}}; (_) -> error end,
                                               {tuple, PBelow}),
                    Outside = ast_lib:mk_intersection([Smallest, ast_lib:mk_negation(Largest)]),
                    case subty:is_subty(SymTab, Outside, {predef, none}) of
                        true -> none;       % the argument might stay inside the refinements
                        false -> {ok, Top}
                    end
            end
    end.

% The smallest instance of a type over all assignments of its variables:
% none() at covariant, any() at contravariant positions. A named type with
% variables among its arguments has unknown variance and gives none.
-spec smallest_instance(ast:ty(), 0 | 1) -> {ok, ast:ty()} | none.
smallest_instance({var, V}, 0) when is_atom(V) -> {ok, {predef, none}};
smallest_instance({var, V}, 1) when is_atom(V) -> {ok, {predef, any}};
smallest_instance({tuple, Ts}, P) -> smallest_list(Ts, P, fun(L) -> {tuple, L} end);
smallest_instance({union, Ts}, P) -> smallest_list(Ts, P, fun(L) -> {union, L} end);
smallest_instance({intersection, Ts}, P) -> smallest_list(Ts, P, fun(L) -> {intersection, L} end);
smallest_instance({list, A}, P) -> smallest_list([A], P, fun([X]) -> {list, X} end);
smallest_instance({nonempty_list, A}, P) -> smallest_list([A], P, fun([X]) -> {nonempty_list, X} end);
smallest_instance({cons, H, R}, P) -> smallest_list([H, R], P, fun([X, Y]) -> {cons, X, Y} end);
smallest_instance({negation, T}, P) ->
    case smallest_instance(T, 1 - P) of {ok, X} -> {ok, {negation, X}}; none -> none end;
smallest_instance({fun_full, As, R}, P) ->
    case {smallest_list(As, 1 - P, fun(L) -> L end), smallest_instance(R, P)} of
        {{ok, As2}, {ok, R2}} -> {ok, {fun_full, As2, R2}};
        _ -> none
    end;
smallest_instance({map, Assocs}, P) ->
    Rs = [{K, smallest_instance(KT, P), smallest_instance(VT, P)} || {K, KT, VT} <- Assocs],
    case lists:all(fun({_, {ok, _}, {ok, _}}) -> true; (_) -> false end, Rs) of
        true -> {ok, {map, [{K, KT, VT} || {K, {ok, KT}, {ok, VT}} <- Rs]}};
        false -> none
    end;
smallest_instance(T, _) ->
    case sets:is_empty(tyutils:free_in_ty(T)) of true -> {ok, T}; false -> none end.

-spec smallest_list([ast:ty()], 0 | 1, fun(([ast:ty()]) -> ast:ty() | [ast:ty()])) -> {ok, ast:ty() | [ast:ty()]} | none.
smallest_list(Ts, P, Build) ->
    Rs = [smallest_instance(T, P) || T <- Ts],
    case lists:all(fun({ok, _}) -> true; (none) -> false end, Rs) of
        true -> {ok, Build([X || {ok, X} <- Rs])};
        false -> none
    end.

-spec overlaps(symtab:t(), [ast:ty()], [ast:ty()]) -> boolean().
overlaps(SymTab, ArgTys, ParamTys) ->
    lists:all(
        fun({{var, _}, _}) -> true; % nothing known about this argument
           ({ArgTy, ParamTy}) ->
                not subty:is_subty(SymTab, ast_lib:mk_intersection([ArgTy, ParamTy]), stdtypes:tnone())
        end,
        lists:zip(ArgTys, ParamTys)).

-spec tally(symtab:t(), constr:collected_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()).

-spec tally(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs0, SubtyConstrs, Maters, UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),
    InlinedConstrs = resolve_overloads(SymTab, InlinedConstrs0),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- InternalRawConstraints],

    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),
    ?METRIC(poly_vars, var_metrics(FixedVars, InternalRawConstraints, SymTab)),

    InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),

    Free = tyutils:free_in_subty_constrs(InlinedConstrs),
    case InternalResult of
        {error, []} -> {error, []};
        _ ->
            % transform to subst:t()
            Sigmas = [subst:mk_tally_subst(
               sets:union(FixedVars, Free),
               maps:from_list([{VarName, ty_parser:unparse(Ty)}
                               || {{var, _, VarName, _}, Ty} <- maps:to_list(Subst)])) % FIXME depends on internal ty_variable representation
             || Subst <- InternalResult],

            lists:map(
              fun({tally_subst, S, Fixed}) ->
                MaterSubst = maps:fold(fun(Var, Ty, MAcc) ->
                    maps:put(Var, subst:apply_base(S, Ty), MAcc)
                  end,
                  #{}, UnificationSubst),
                gradual_utils:postprocess({tally_subst, maps:merge(S, MaterSubst), Fixed}, SubtyConstrs, Maters, SymTab)
              end,
              Sigmas)
      end.

-spec split([{ast:ty(), ast:ty()}], monomorphic_variables()) -> constraints_partition().
split(Constrs, FixedVars) ->
    % Phase 1: Build Union-Find by connecting variables that co-occur in constraints.
    %          Also track constraint index -> variable mapping for grouping.
    {UF, IndexedConstrs, _} = lists:foldl(fun(Entry, {AccUF, AccIdx, I}) ->
        Vars = varset(Entry, FixedVars),
        case Vars of
            [] ->
                % Ground constraint: tag with a deterministic per-call key so
                % partition iteration order is reproducible 
                {AccUF, [{{ground, I}, Entry} | AccIdx], I + 1};
            [First | Rest] ->
                UF1 = uf_ensure(First, AccUF),
                UF2 = lists:foldl(fun(V, U) ->
                    uf_union(First, V, uf_ensure(V, U))
                end, UF1, Rest),
                {UF2, [{First, Entry} | AccIdx], I + 1}
        end
    end, {#{}, [], 0}, Constrs),

    % Phase 2: Group constraints by their root representative.
    lists:foldl(fun({Key, Entry}, Acc) ->
        GroupKey = case Key of
            {ground, _} -> Key;
            _ -> {Root, _} = uf_find(Key, UF), Root
        end,
        maps:update_with(GroupKey, fun(Old) -> [Entry | Old] end, [Entry], Acc)
    end, #{}, IndexedConstrs).

-spec varset({ast:ty(), ast:ty()}, monomorphic_variables()) -> [ast:ty_var()].
varset(Constraint, FixedVars) ->
    lists:usort(utils:everything(fun
            ({var, N} = Var) when is_atom(N) ->
                case sets:is_element(N, FixedVars) of
                    true -> error;
                    _ -> {ok, Var}
                end;
            (_) -> error
        end, Constraint)).

%% Union-Find with path compression (functional, returns updated parent map).
-spec uf_ensure(ast:ty_var(), map()) -> map().
uf_ensure(V, Parent) ->
    case maps:is_key(V, Parent) of
        true -> Parent;
        false -> maps:put(V, V, Parent)
    end.

-spec uf_find(ast:ty_var(), map()) -> {ast:ty_var(), map()}.
uf_find(V, Parent) ->
    case maps:get(V, Parent) of
        V -> {V, Parent};
        P ->
            {Root, Parent1} = uf_find(P, Parent),
            {Root, maps:put(V, Root, Parent1)}
    end.

-spec uf_union(ast:ty_var(), ast:ty_var(), map()) -> map().
uf_union(A, B, Parent) ->
    {RootA, Parent1} = uf_find(A, Parent),
    {RootB, Parent2} = uf_find(B, Parent1),
    case RootA =:= RootB of
        true -> Parent2;
        false -> maps:put(RootB, RootA, Parent2)
    end.

-ifdef(TEST).

chain_test() ->
    global_state:with_new_state(fun() ->
        T = tvar('T'), B = tvar('B'),
        Usort = {intersection, [{fun_full, [{nonempty_list, T}], {nonempty_list, T}},
                                {fun_full, [{list, T}], {list, T}}]},
        Ground = {list, stdtypes:tatom()},
        % list(atom()) holds [], which no nonempty_list(T) does: the last clause applies
        [{scsubty, _, {fun_full, [{list, T}], {list, T}}, {fun_full, [Ground], B}}] =
            resolve_overload(symtab:empty(), {scsubty, ast:loc_auto(), Usort, {fun_full, [Ground], B}}),
        % a non-empty list may sit inside the first clause for some T: untouched
        C2 = {scsubty, ast:loc_auto(), Usort, {fun_full, [{nonempty_list, stdtypes:tatom()}], B}},
        [C2] = resolve_overload(symtab:empty(), C2),
        % list(B) holds [] for every B: resolved as well
        [{scsubty, _, {fun_full, [{list, T}], {list, T}}, _}] =
            resolve_overload(symtab:empty(), {scsubty, ast:loc_auto(), Usort, {fun_full, [{list, B}], B}}),
        % nonempty_list(B) may be empty (B = none()): no witness, untouched
        C4 = {scsubty, ast:loc_auto(), Usort, {fun_full, [{nonempty_list, B}], B}},
        [C4] = resolve_overload(symtab:empty(), C4)
    end).

partition_test() ->
    A = tvar('A'), B = tvar('B'),
    C = tvar('C'), D = tvar('D'),
    E = tvar('E'), F = tvar('F'),

    2 = maps:size(split([ {A, B}, {C, D} ], sets:new())),
    3 = maps:size(split([ {A, B}, {C, D}, {E, F} ], sets:new())),
    2 = maps:size(split([ {A, B}, {B, C}, {D, D} ], sets:new())),
    1 = maps:size(split([ {A, B}, {B, C}, {C, D}, {D, A} ], sets:new())),
    2 = maps:size(split([ {A, B}, {B, C}, {C, D}, {D, A} ], sets:from_list(['D', 'A']))),

    ok.

%% Ground constraints (no free vars) should not merge independent partitions.
%% A ground constraint like {integer(), atom()} has no type variables, so its varset is [].
%% It should go into its own partition, not cause all other partitions to collapse into one.
partition_ground_test() ->
    A = tvar('A'), B = tvar('B'),
    C = tvar('C'), D = tvar('D'),
    Ground1 = {{predef, integer}, {predef, atom}},
    Ground2 = {{predef, float}, {predef, number}},

    % Single ground constraint with variable partitions: should be 3 partitions
    3 = maps:size(split([ {A, B}, Ground1, {C, D} ], sets:new())),
    % Two ground constraints should be 2 separate partitions, not merged into 1
    2 = maps:size(split([ Ground1, Ground2 ], sets:new())),
    % Two ground + two variable partitions = 4 partitions
    4 = maps:size(split([ {A, B}, Ground1, {C, D}, Ground2 ], sets:new())),

    ok.

-endif.
