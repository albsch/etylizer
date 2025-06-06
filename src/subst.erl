-module(subst).

-compile({no_auto_import,[apply/2, apply/3]}).

-include("log.hrl").

-export_type([
    t/0,
    base_subst/0
]).

-export([
    apply/2,
    apply/3,
    from_list/1,
    empty/0,
    extend/3,
    mk_tally_subst/2,
    base_subst/1
]).

-ifdef(TEST).
-export([
    clean/2   
]).
-endif.


-type base_subst() :: #{ ast:ty_varname() => ast:ty() }.

-type tally_subst() :: {tally_subst, base_subst(), sets:set(ast:ty_varname())}.

-type t() :: base_subst() | tally_subst().

-spec base_subst(t()) -> base_subst().
base_subst({tally_subst, S, _}) -> S;
base_subst(S) -> S.

-spec clean(ast:ty(), sets:set(ast:ty_varname())) -> ast:ty().
clean(T, Fixed) ->
    % clean
    Cleaned = clean_type(T, Fixed),
    % simplify by converting into internal type and back (processes any() and none() replacements)
    Res = ast_lib:erlang_ty_to_ast(X = ast_lib:ast_to_erlang_ty(Cleaned, symtab:empty())), % TODO symtab?
    % FIXME remove sanity at some point
    true = ty_rec:is_subtype(X, ast_lib:ast_to_erlang_ty(T, symtab:empty())),
    Res.

-spec apply(t(), ast:ty()) -> ast:ty().
apply(Subst, T) ->
    apply(Subst, T, clean).

-type clean_mode() :: clean | no_clean.

-spec apply(t(), ast:ty(), clean_mode()) -> ast:ty().
apply(Subst = {tally_subst, BaseSubst, Fixed}, T, CleanMode) ->
    U = apply_base(BaseSubst, T),
    Res =
        case CleanMode of
            clean -> clean(U, Fixed);
            no_clean -> U
        end,
    ?LOG_TRACE("subst:apply, T=~s, Subst=~s, U=~s, Res=~s",
        pretty:render_ty(T),
        pretty:render_subst(Subst),
        pretty:render_ty(U),
        pretty:render_ty(Res)),
    Res;
apply(S, T, _) -> apply_base(S, T).

-spec apply_base(base_subst(), ast:ty()) -> ast:ty().
apply_base(S, T) ->
    case T of
        {singleton, _} -> T;
        % TODO full bitstring support
        {bitstring} -> T;
        % {binary, _, _} -> T;
        {empty_list} -> T;
        {list, U} -> {list, apply_base(S, U)};
        {mu, V, U} -> {mu, V, apply_base(S, U)};
        {nonempty_list, U} -> {nonempty_list, apply_base(S, U)};
        {improper_list, U, V} -> {improper_list, apply_base(S, U), apply_base(S, V)};
        {nonempty_improper_list, U, V} -> {nonempty_improper_list, apply_base(S, U), apply_base(S, V)};
        {fun_simple} -> T;
        {fun_any_arg, U} -> {fun_any_arg, apply_base(S, U)};
        {fun_full, Args, U} -> {fun_full, apply_list(S, Args), apply_base(S, U)};
        {range, _, _} -> T;
        {map_any} -> T;
        {map, Assocs} ->
            {map, lists:map(fun({Kind, U, V}) -> {Kind, apply_base(S, U), apply_base(S, V)} end, Assocs)};
        {predef, _} -> T;
        {predef_alias, _} -> T;
        {record, Name, Fields} ->
            {record, Name,
             lists:map(fun({FieldName, U}) -> {FieldName, apply_base(S, U)} end, Fields)};
        {named, Loc, Ref, Args} ->
            {named, Loc, Ref, apply_list(S, Args)};
        {tuple_any} -> T;
        {tuple, Args} -> {tuple, apply_list(S, Args)};
        {var, Alpha} ->
            case maps:find(Alpha, S) of
                error -> {var, Alpha};
                {ok, U} -> U
            end;
        {union, Args} -> {union, apply_list(S, Args)};
        {intersection, Args} -> {intersection, apply_list(S, Args)};
        {negation, U} -> {negation, apply_base(S, U)}
    end.

-spec apply_list(base_subst(), [ast:ty()]) -> [ast:ty()].
apply_list(S, L) -> lists:map(fun(T) -> apply_base(S, T) end, L).

-spec extend(t(), ast:ty_varname(), ast:ty()) -> t().
extend({tally_subst, BaseSubst, Fixed}, Alpha, T) ->
    {tally_subst, extend(BaseSubst, Alpha, T), Fixed};
extend(BaseSubst, Alpha, T) ->
    maps:put(Alpha, T, BaseSubst).

-spec from_list([{ast:ty_varname(), ast:ty()}]) -> t().
from_list(L) -> maps:from_list(L).

-spec empty() -> t().
empty() -> #{}.

-spec mk_tally_subst(sets:set(ast:ty_varname()), base_subst()) -> t().
mk_tally_subst(Fixed, Base) -> {tally_subst, Base, Fixed}.

clean_type(Ty, Fix) ->
    %% collect ALL vars in all positions
    %% if a var is only in co variant position, replace with 0
    %% if a var is only in contra variant position, replace with 1
    VarPositions = collect_vars(Ty, 0, #{}, Fix),

    NoVarsDnf = maps:fold(
        fun(VariableName, VariablePositions, Tyy) ->
            case lists:usort(VariablePositions) of
                [0] ->
                    % !a => none
                    %  a => none
                    % FIXME (SW, 2023-12-08): this has bad performance. Better build one substitution
                    % and apply it once.
                    R = apply_base(#{VariableName => {predef, none}}, Tyy),
                    R;
                [1] ->
                    apply_base(#{VariableName => {predef, any}}, Tyy);
                _ -> Tyy
            end
        end, Ty, VarPositions),

    Cleaned = NoVarsDnf,
    Cleaned.

combine_vars(_K, V1, V2) ->
    V1 ++ V2.

collect_vars({K, Components}, CPos, Pos, Fix) when K == union; K == intersection; K == tuple; K == map ->
    VPos = lists:map(fun(Ty) -> collect_vars(Ty, CPos, Pos, Fix) end, Components),
    lists:foldl(fun(FPos, Current) -> maps:merge_with(fun combine_vars/3, FPos, Current) end, #{}, VPos);
collect_vars({fun_full, Components, Target}, CPos, Pos, Fix) ->
    VPos = lists:map(fun(Ty) -> collect_vars(Ty, 1 - CPos, Pos, Fix) end, Components),
    M1 = lists:foldl(fun(FPos, Current) -> maps:merge_with(fun combine_vars/3, FPos, Current) end, #{}, VPos),
    M2 = collect_vars(Target, CPos, Pos, Fix),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({negation, Ty}, CPos, Pos, Fix) -> collect_vars(Ty, 1 - CPos, Pos, Fix);
collect_vars({predef, _}, _CPos, Pos, _) -> Pos;
collect_vars({predef_alias, _}, _CPos, Pos, _) -> Pos;
collect_vars({singleton, _}, _CPos, Pos, _) -> Pos;
collect_vars({range, _, _}, _CPos, Pos, _) -> Pos;
collect_vars({_, any}, _CPos, Pos, _) -> Pos;
collect_vars({empty_list}, _CPos, Pos, _) -> Pos;
collect_vars({bitstring}, _CPos, Pos, _) -> Pos;
collect_vars({map_any}, _CPos, Pos, _) -> Pos;
collect_vars({tuple_any}, _CPos, Pos, _) -> Pos;
collect_vars({fun_simple}, _CPos, Pos, _) -> Pos;
collect_vars({list, A}, CPos, Pos, Fix) ->
    collect_vars(A, CPos, Pos, Fix);
collect_vars({mu, MuVar, A}, CPos, Pos, Fix) ->
    % hack: recursion variables are not really fixed variables, but can be considered as such for cleaning (i.e. don't touch them)
    collect_vars(A, CPos, Pos, sets:union(Fix, sets:from_list([MuVar]))); 
collect_vars({Map, A, B}, CPos, Pos, Fix) when Map == map_field_opt; Map == map_field_req ->
    M1 = collect_vars(A, CPos, Pos, Fix),
    M2 = collect_vars(B, CPos, Pos, Fix),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({improper_list, A, B}, CPos, Pos, Fix) ->
    M1 = collect_vars(A, CPos, Pos, Fix),
    M2 = collect_vars(B, CPos, Pos, Fix),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({var, Name}, CPos, Pos, Fix) ->
    case sets:is_element(Name, Fix) of
        true -> Pos;
        _ ->
            AllPositions = maps:get(Name, Pos, []),
            Pos#{Name => AllPositions ++ [CPos]}
    end;
collect_vars(Ty, _, _, _) ->
    logger:error("Unhandled collect vars branch: ~p", [Ty]),
    errors:bug("Unhandled collect vars branch").
