-module(constr_gen).

-include_lib("log.hrl").

-export([
         gen_constrs_fun_group/1, gen_constrs_annotated_fun/2,
         sanity_check/2
        ]).

-compile([nowarn_shadow_vars]).

-record(ctx,
        { var_counter :: counters:counters_ref()
        }).
-type ctx() :: #ctx{}.

-spec new_ctx() -> ctx().
new_ctx() ->
    Counter = counters:new(2, []),
    Ctx = #ctx{ var_counter = Counter },
    Ctx.

-spec fresh_tyvar(ctx()) -> ast:ty_var().
fresh_tyvar(Ctx) ->
    I = counters:get(Ctx#ctx.var_counter, 1),
    counters:add(Ctx#ctx.var_counter, 1, 1),
    S = utils:sformat("$~w", I),
    {var, list_to_atom(S)}.

-spec fresh_vars(ctx(), arity()) -> [ast:local_varname()].
fresh_vars(Ctx, N) ->
    I = counters:get(Ctx#ctx.var_counter, 2),
    counters:add(Ctx#ctx.var_counter, 2, 1),
    Loop =
        fun Loop(J) ->
                if
                    J > N -> [];
                    true ->
                        ArgJ = list_to_atom(utils:sformat("A~w", J)),
                        X = {ArgJ, I},
                        [X | Loop(J + 1)]
                end
        end,
    Loop(1).

-spec single(T) -> sets:set(T).
single(X) -> sets:from_list([X]).

-spec mk_locs(string(), ast:loc()) -> constr:locs().
mk_locs(Label, X) -> {Label, single(X)}.

% Inference for a group of mutually recursive functions without type annotations.
-spec gen_constrs_fun_group([ast:fun_decl()]) -> {constr:constrs(), constr:constr_env()}.
gen_constrs_fun_group(Decls) ->
    Ctx = new_ctx(),
    lists:foldl(
      fun({function, L, Name, Arity, FunClauses}, {Cs, Env}) ->
              Exp = {'fun', L, no_name, FunClauses},
              Alpha = fresh_tyvar(Ctx),
              ThisCs = exp_constrs(Ctx, Exp, Alpha),
              Ref = {ref, Name, Arity},
              {sets:union(ThisCs, Cs), maps:put(Ref, Alpha, Env)}
      end, {sets:new(), #{}}, Decls).

% Checking the type spec of a function.
% This function is invoked for each branch of the intersection type in the type spec.
% The idea is that we can give better error messages by pointing out which part of the
% intersection did not type check.
-spec gen_constrs_annotated_fun(ast:ty_full_fun(), ast:fun_decl()) -> constr:constrs().
gen_constrs_annotated_fun({fun_full, ArgTys, ResTy}, {function, L, Name, Arity, FunClauses}) ->
    Ctx = new_ctx(),
    {Args, Body} = fun_clauses_to_exp(Ctx, L, FunClauses),
    if length(Args) =/= length(ArgTys) orelse length(Args) =/= Arity ->
            errors:ty_error(L, "Arity mismatch for function ~w", Name);
       true -> ok
    end,
    ArgRefs = lists:map(fun(V) -> {local_ref, V} end, Args),
    Env = maps:from_list(lists:zip(ArgRefs, ArgTys)),
    BodyCs = exp_constrs(Ctx, Body, ResTy),
    Msg = utils:sformat("definition of ~w/~w", Name, Arity),
    single({cdef, mk_locs(Msg, L), Env, BodyCs}).

-spec exps_constrs(ctx(), ast:loc(), [ast:exp()], ast:ty()) -> constr:constrs().
exps_constrs(Ctx, L, Es, T) ->
    case lists:reverse(Es) of
        [] -> single({cunsatisfiable, L, "empty list of expressions"});
        [Last | Init] ->
            Cs0 = exp_constrs(Ctx, Last, T),
            lists:foldl(fun (E, Acc) ->
                                Alpha = fresh_tyvar(Ctx),
                                Cs = exp_constrs(Ctx, E, Alpha),
                                % Question: Constraint Alpha to unit?
                                sets:union(Acc, Cs)
                        end,
                        Cs0,
                        Init)
    end.

-spec exp_constrs(ctx(), ast:exp(), ast:ty()) -> constr:constrs().
exp_constrs(Ctx, E, T) ->
    case E of
        {'atom', L, A} -> single({csubty, mk_locs("atom literal", L), {singleton, A}, T});
        {'char', L, C} -> single({csubty, mk_locs("char literal", L), {singleton, C}, T});
        {'integer', L, I} -> single({csubty, mk_locs("int literal", L), {singleton, I}, T});
        {'float', L, _F} -> single({csubty, mk_locs("float literal", L), {predef, float}, T});
        {'string', L, ""} -> single({csubty, mk_locs("empty string literal", L), {empty_list}, T});
        {'string', L, _S} -> single({csubty, mk_locs("string literal", L), {predef_alias, string}, T});
        {bc, L, _E, _Qs} -> errors:unsupported(L, "bitstrings");
        {block, L, Es} -> exps_constrs(Ctx, L, Es, T);
        {'case', L, ScrutE, Clauses} ->
            Alpha = fresh_tyvar(Ctx),
            Beta = fresh_tyvar(Ctx),
            Cs0 = exp_constrs(Ctx, ScrutE, Alpha),
            {BodyList, _Lowers, Uppers, CsCases} =
                lists:foldl(fun (Clause = {case_clause, LocClause, _, _, _},
                                 {BodyList, Lowers, Uppers, AccCs}) ->
                                    ?LOG_TRACE("Generating constraint for case clause at ~s: Lowers=~s, Uppers=~s",
                                               ast:format_loc(LocClause),
                                               pretty:render_tys(Lowers),
                                               pretty:render_tys(Uppers)),
                                    {ThisLower, ThisUpper, ThisCs, ThisConstrBody} =
                                        case_clause_constrs(
                                          Ctx,
                                          ty_without(Alpha, ast:mk_union(Lowers)),
                                          ScrutE,
                                          Clause,
                                          Beta),
                                    {BodyList ++ [ThisConstrBody],
                                     Lowers ++ [ThisLower],
                                     Uppers ++ [ThisUpper],
                                     sets:union(ThisCs, AccCs)}
                            end,
                            {[], [], [], sets:new()},
                            Clauses),
            AllCs = sets:union([Cs0, CsCases,
                                single({csubty, mk_locs("exhaustiveness check", L),
                                        Alpha, ast:mk_union(Uppers)})]),
            sets:from_list([
                {ccase, mk_locs("case", L), AllCs, BodyList},
                {csubty, mk_locs("result of case", L), Beta, T}
            ]);
        {'catch', L, CatchE} ->
            Top = {predef, any},
            Cs = exp_constrs(Ctx, CatchE, Top),
            sets:add_element({csubty, mk_locs("result of catch", L), Top, T}, Cs);
        {cons, L, Head, Tail} ->
            Alpha = fresh_tyvar(Ctx),
            CsHead = exp_constrs(Ctx, Head, Alpha),
            CsTail = exp_constrs(Ctx, Tail, T),
            sets:add_element({csubty, mk_locs("result of cons", L), {list, Alpha}, T},
                             sets:union(CsHead, CsTail));
        {fun_ref, L, GlobalRef} ->
            single({cvar, mk_locs("function ref", L), GlobalRef, T});
        {'fun', L, RecName, FunClauses} ->
            {Args, BodyExp} = fun_clauses_to_exp(Ctx, L, FunClauses),
            ArgTys = lists:map(fun(X) -> {{local_ref, X}, fresh_tyvar(Ctx)} end, Args),
            ArgEnv = maps:from_list(ArgTys),
            ResTy = fresh_tyvar(Ctx),
            FunTy = {fun_full, lists:map(fun({_, Ty}) -> Ty end, ArgTys), ResTy},
            CsBody = exp_constrs(Ctx, BodyExp, ResTy),
            BodyEnv =
                case RecName of
                    no_name -> ArgEnv;
                    {local_bind, F} -> maps:put({local_ref, F}, FunTy, ArgEnv)
                end,
            sets:from_list([{cdef, mk_locs("function def", L), BodyEnv, CsBody},
                            {csubty, mk_locs("result of function def", L), FunTy, T}]);
        {call, L, FunExp, Args} ->
            {ArgCs, ArgTys} =
                lists:foldr(
                  fun(ArgExp, {AccCs, AccTys}) ->
                          Alpha = fresh_tyvar(Ctx),
                          Cs = exp_constrs(Ctx, ArgExp, Alpha),
                          {sets:union(AccCs, Cs), [Alpha | AccTys]}
                  end,
                  {sets:new(), []},
                  Args),
            Beta = fresh_tyvar(Ctx),
            FunTy = {fun_full, ArgTys, Beta},
            FunCs = exp_constrs(Ctx, FunExp, FunTy),
            sets:add_element(
              {csubty, mk_locs("result of function call", L), Beta, T},
              sets:union(FunCs, ArgCs));
        {call_remote, L, _ModExp, _FunExp, _Args} ->
            errors:unsupported(L, "function calls with dynamically computed modules");
        ({'if', _, _} = IfExp) ->
            exp_constrs(Ctx, if_exp_to_case_exp(IfExp), T);
        {lc, _L, _E, _Qs} -> sets:new(); % FIXME
        {map_create, _L, _Assocs} -> sets:new(); % FIXME
        {map_update, _L, _MapExp, _Assocs} -> sets:new(); % FIXME
        {nil, L} ->
            single({csubty, mk_locs("result of nil", L), {empty_list}, T});
        {op, L, Op, Lhs, Rhs} ->
            Alpha1 = fresh_tyvar(Ctx),
            Cs1 = exp_constrs(Ctx, Lhs, Alpha1),
            Alpha2 = fresh_tyvar(Ctx),
            Cs2 = exp_constrs(Ctx, Rhs, Alpha2),
            Beta = fresh_tyvar(Ctx),
            MsgArg = utils:sformat("args of op ~w", Op),
            MsgRes = utils:sformat("result of op ~w", Op),
            OpCs = sets:from_list(
                     [{cop, mk_locs(MsgArg, L), Op, 2, {fun_full, [Alpha1, Alpha2], Beta}},
                      {csubty, mk_locs(MsgRes, L), Beta, T}]),
            sets:union([Cs1, Cs2, OpCs]);
        {op, L, Op, Arg} ->
            Alpha = fresh_tyvar(Ctx),
            ArgCs = exp_constrs(Ctx, Arg, Alpha),
            Beta = fresh_tyvar(Ctx),
            MsgArg = utils:sformat("arg of op ~w", Op),
            MsgRes = utils:sformat("result of op ~w", Op),
            OpCs = sets:from_list(
                     [{cop, mk_locs(MsgArg, L), Op, 1, {fun_full, [Alpha], Beta}},
                      {csubty, mk_locs(MsgRes, L), Beta, T}]),
            sets:union(ArgCs, OpCs);
        {'receive', _L, _CaseClauses} -> sets:new(); % FIXME
        {receive_after, _L, _CauseClauses, _TimeoutExp, _Body} -> sets:new(); % FIXME
        {record_create, _L, _Name, _Fields} -> sets:new(); % FIXME
        {record_field, _L, _Exp, _Name, _Field} -> sets:new(); % FIXME
        {record_index, _L, _Name, _Field} -> sets:new(); % FIXME
        {record_update, _L, _Exp, _Name, _Fields} -> sets:new(); % FIXME
        {tuple, L, Args} ->
            {Tys, Cs} =
                lists:foldr(
                  fun(Arg, {Tys, Cs}) ->
                          Alpha = fresh_tyvar(Ctx),
                          ThisCs = exp_constrs(Ctx, Arg, Alpha),
                          {[Alpha | Tys], sets:union(Cs, ThisCs)}
                  end,
                  {[], sets:new()},
                  Args),
            TupleC = {csubty, mk_locs("tuple constructor", L), {tuple, Tys}, T},
            sets:add_element(TupleC, Cs);
        {'try', _L, _Exps, _CaseClauses, _CatchClauses, _AfterBody} -> sets:new(); % FIXME
        {var, L, AnyRef} ->
            Msg = utils:sformat("var ~s", pretty:render(pretty:ref(AnyRef))),
            single({cvar, mk_locs(Msg, L), AnyRef, T});
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec ty_without(ast:ty(), ast:ty()) -> ast:ty().
ty_without(T1, T2) -> ast:mk_intersection([T1, ast:mk_negation(T2)]).

-spec case_clause_constrs(ctx(), ast:ty(), ast:exp(), ast:case_clause(), ast:ty())
                         -> {ast:ty(), ast:ty(), constr:constrs(), constr:constr_case_body()}.
case_clause_constrs(Ctx, TyScrut, Scrut, {case_clause, L, Pat, Guards, Exps}, Beta) ->
    {Upper, Lower} = pat_guard_upper_lower(Pat, Guards, Scrut),
    Ti = ast:mk_intersection([TyScrut, Upper]),
    {Ci0, Gamma0} = pat_env(Ctx, L, Ti, pat_of_exp(Scrut)),
    {Ci1, Gamma1} = pat_guard_env(Ctx, L, Ti, Pat, Guards),
    Gamma2 = intersect_envs(Gamma1, Gamma0),
    ?LOG_TRACE("TyScrut=~w, Scrut=~w, Gamma0=~w, Gamma1=~w, Gamma2=~w",
               TyScrut, Scrut, Gamma0, Gamma1, Gamma2),
    InnerCs = exps_constrs(Ctx, L, Exps, Beta),
    CGuards =
        sets:union(
          lists:map(
            fun(Guard) ->
                    exps_constrs(Ctx, L, Guard, {predef_alias, boolean})
            end,
            Guards)),
    ConstrBody = {mk_locs("case branch", L), Gamma2, CGuards, InnerCs, Ti}, % Gamma in InnerCs when Ti
    {Lower, Upper, sets:union([Ci0, Ci1]), ConstrBody}.


% ⌊ p when g ⌋_e and ⌈ p when g ⌉_e
-spec pat_guard_upper_lower(ast:pat(), [ast:guard()], ast:exp()) -> {ast:ty(), ast:ty()}.
pat_guard_upper_lower(P, Gs, E) ->
    % Env has type constr:constr_env() = #{ast:any_ref() => ast:ty()}
    {Env, Status} = guard_seq_env(Gs),
    EPat = pat_of_exp(E),
    PatTy = ty_of_pat(Env, P),
    ETy = ty_of_pat(Env, EPat),
    Upper = ast:mk_intersection([PatTy, ETy]),
    VarsOfGuards = sets:from_list(lists:filtermap(fun ast:local_varname_from_any_ref/1, maps:keys(Env))),
    BoundVars = sets:union(bound_vars_pat(P), bound_vars_pat(EPat)),
    Lower =
        case {Status, sets:is_subset(VarsOfGuards, BoundVars)} of
            {safe, true} -> Upper;
            _ -> {predef, none}
        end,
    ?LOG_TRACE("EPat=~200p, PatTy=~s, ETy=~s, Upper=~s, Lower=~s, VarsOfGuards=~200p, BoundVars=~w, Status=~w",
               EPat,
               pretty:render_ty(PatTy),
               pretty:render_ty(ETy),
               pretty:render_ty(Upper),
               pretty:render_ty(Lower),
               maps:keys(Env),
               sets:to_list(BoundVars),
               Status),
    {Upper, Lower}.

-spec bound_vars_pat(ast:pat()) -> sets:set(ast:local_varname()).
bound_vars_pat(P) ->
    case P of
        {'atom', _L, _A} -> sets:new();
        {'char', _L, _C} -> sets:new();
        {'integer', _L, _I} -> sets:new();
        {'float', _L, _F} -> sets:new();
        {'string', _L, _S} -> sets:new();
        {bin, L, _Elems} -> errors:unsupported(L, "bitstring patterns");
        {match, _L, P1, P2} ->
            sets:union(bound_vars_pat(P1), bound_vars_pat(P2));
        {nil, _L} -> sets:new();
        {cons, _L, P1, P2} ->
            sets:union(bound_vars_pat(P1), bound_vars_pat(P2));
        {op, _L, _Op, Ps} ->
            lists:foldl(
              fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new(),
              Ps
             );
        {map, L, _Assocs} -> errors:unsupported(L, "map patterns");
        {record, L, _Name, _Fields} -> errors:unsupported(L, "record patterns");
        {record_index, L, _Name, _Field} -> errors:unsupported(L, "record index patterns");
        {tuple, _L, Ps} ->
            lists:foldl(
              fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new(),
              Ps
             );
        {wildcard, _L} -> sets:new();
        {var, _L, {local_bind, V}} -> sets:from_list([V]);
        {var, _L, {local_ref, _V}} -> sets:new()
    end.


% \lbag p \rbag_\Gamma
-spec ty_of_pat(constr:constr_env(), ast:pat()) -> ast:ty().
ty_of_pat(Env, P) ->
    case P of
        {'atom', _L, A} -> {singleton, A};
        {'char', _L, C} -> {singleton, C};
        {'integer', _L, I} -> {singleton, I};
        {'float', _L, _F} -> {predef, float};
        {'string', _L, _S} -> {predef_alias, string};
        {bin, L, _Elems} -> errors:unsupported(L, "bitstring patterns");
        {match, _L, P1, P2} -> ast:mk_intersection([ty_of_pat(Env, P1), ty_of_pat(Env, P2)]);
        {nil, _L} -> {empty_list};
        {cons, _L, P1, P2} ->
            %% FIXME: this is wrong. It should be the union of {list, ty_of_pat(Env, P1)}
            %% and ty_of_pat(Env, P2), intersected with type list(any()).
            %% Accepting and potential types of list patterns are also wrong.
            ast:mk_intersection([{list, ty_of_pat(Env, P1)}, ty_of_pat(Env, P2)]);
        {op, _, '++', [P1, P2]} ->
            ast:mk_intersection([ty_of_pat(Env, P1), ty_of_pat(Env, P2), {predef_alias, list}]);
        {op, _, '-', [SubP]} ->
            ast:mk_intersection([ty_of_pat(Env, SubP), {predef_alias, number}]);
        {op, L, Op, _} -> errors:unsupported(L, "operator ~w in patterns", Op);
        {map, L, _Assocs} -> errors:unsupported(L, "map patterns");
        {record, L, _Name, _Fields} -> errors:unsupported(L, "record patterns");
        {record_index, L, _Name, _Field} -> errors:unsupported(L, "record index patterns");
        {tuple, _L, Ps} -> {tuple, lists:map(fun(P) -> ty_of_pat(Env, P) end, Ps)};
        {wildcard, _L} -> {predef, any};
        {var, _L, {local_bind, V}} -> maps:get({local_ref, V}, Env, {predef, any});
        {var, _L, {local_ref, _V}} -> {predef, any} % we could probably do better here
    end.

% t // pg
-spec pat_guard_env(ctx(), ast:loc(), ast:ty(), ast:pat(), [ast:guard()]) ->
          {const:constrs(), constr:constr_env()}.
pat_guard_env(Ctx, L, T, P, Gs) ->
    {Cs, Env} = pat_env(Ctx, L, T, P),
    {EnvGuards, _} = guard_seq_env(Gs),
    {Cs, intersect_envs(Env, EnvGuards)}.

% t // p
-spec pat_env(ctx(), ast:loc(), ast:ty(), ast:pat()) -> {const:constrs(), constr:constr_env()}.
pat_env(Ctx, OuterL, T, P) ->
    Empty = {sets:new(), #{}},
    case P of
        {'atom', _L, _A} -> Empty;
        {'char', _L, _C} -> Empty;
        {'integer', _L, _I} -> Empty;
        {'float', _L, _F} -> Empty;
        {'string', _L, _S} -> Empty;
        {bin, L, _Elems} -> errors:unsupported(L, "bitstring patterns");
        {match, _L, P1, P2} ->
            {Cs1, Env1} = pat_env(Ctx, OuterL, T, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, T, P2),
            {sets:union(Cs1, Cs2), intersect_envs(Env1, Env2)};
        {nil, _L} ->
            Empty;
        {cons, _L, P1, P2} ->
            Alpha1 = fresh_tyvar(Ctx),
            Alpha2 = fresh_tyvar(Ctx),
            {Cs1, Env1} = pat_env(Ctx, OuterL, Alpha1, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, Alpha2, P2),
            C1 = {csubty, mk_locs("t // [_ | _]", OuterL), T, {list, Alpha1}},
            C2 = {csubty, mk_locs("t // [_ | _]", OuterL), T, Alpha2},
            {sets:add_element(C1, sets:add_element(C2, sets:union(Cs1, Cs2))),
             intersect_envs(Env1, Env2)};
        {op, _L, '++', [P1, P2]} ->
            {Cs1, Env1} = pat_env(Ctx, OuterL, T, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, T, P2),
            {sets:union(Cs1, Cs2), intersect_envs(Env1, Env2)};
        {op, _L, '-', [SubP]} ->
            pat_env(Ctx, OuterL, T, SubP);
        {op, L, Op, _Ps} ->
            errors:unsupported(L, "operator ~w in patterns", Op);
        {map, L, _Assocs} -> errors:unsupported(L, "map patterns");
        {record, L, _Name, _Fields} -> errors:unsupported(L, "record patterns");
        {record_index, L, _Name, _Field} -> errors:unsupported(L, "record index patterns");
        {tuple, _L, Ps} ->
            {Alphas, Cs, Env} =
                lists:foldl(
                  fun (P, {Alphas, Cs, Env}) ->
                          Alpha = fresh_tyvar(Ctx),
                          {ThisCs, ThisEnv} = pat_env(Ctx, OuterL, Alpha, P),
                          {Alphas ++ [Alpha],
                           sets:union(Cs, ThisCs),
                           intersect_envs(Env, ThisEnv)}
                  end,
                  {[], sets:new(), #{}},
                  Ps),
            C = {csubty, mk_locs("t // {...}", OuterL), T, {tuple, Alphas}},
            {sets:add_element(C, Cs), Env};
        {wildcard, _L} ->
            Empty;
        {var, _L, {local_bind, V}} ->
            {sets:new(), #{ {local_ref, V} => T }};
        {var, _L, {local_ref, V}} ->
            {sets:new(), #{ {local_ref, V} => T }}
    end.

% (| e |)
-spec pat_of_exp(ast:exp()) -> ast:pat().
pat_of_exp(E) ->
    Wc = {wildcard, ast:loc_auto()},
    case E of
        {block, _L, Es} ->
            case lists:reverse(Es) of
                [] -> Wc;
                [Last | _] -> pat_of_exp(Last)
            end;
        {cons, _L, Head, Tail} ->
            {cons, ast:loc_auto(), pat_of_exp(Head), pat_of_exp(Tail)};
        {tuple, _L, Args} ->
            {tuple, ast:loc_auto(), lists:map(fun pat_of_exp/1, Args)};
        {var, _L, {local_ref, V}} -> {var, ast:loc_auto(), {local_bind, V}};
        _ -> Wc
    end.

% Γ //\\ Γ
-spec intersect_envs(constr:constr_env(), constr:constr_env()) -> constr:constr_env().
intersect_envs(Env1, Env2) ->
    combine_envs(Env1, Env2, fun(T1, T2) -> ast:mk_intersection([T1, T2]) end).

-spec combine_envs(
        constr:constr_env(),
        constr:constr_env(),
        fun((ast:ty(), ast:ty()) -> ast:ty())
       ) -> constr:constr_env().
combine_envs(Env1, Env2, F) ->
    Keys = sets:from_list(maps:keys(Env1) ++ maps:keys(Env2)),
    sets:fold(
      fun (K, Env) ->
              T1 = maps:get(K, Env1, none),
              T2 = maps:get(K, Env2, none),
              T = case {T1, T2} of
                      {none, X}-> X;
                      {X, none} -> X;
                      _ -> F(T1, T2)
                  end,
              maps:put(K, T, Env)
      end,
      #{},
      Keys
     ).

% Γ \\// Γ
-spec union_envs(constr:constr_env(), constr:constr_env()) -> constr:constr_env().
union_envs(Env1, Env2) ->
    combine_envs(Env1, Env2, fun(T1, T2) -> ast:mk_union([T1, T2]) end).

-spec negate_env(constr:constr_env()) -> constr:constr_env().
negate_env(Env) -> maps:map(fun (_Key, T) -> ast:mk_negation(T) end, Env).

% env(g)
-spec guard_seq_env([ast:guard()]) -> {constr:constr_env(), safe | unsafe}.
guard_seq_env(Guards) ->
    combine_guard_result(Guards, fun guard_env/1, fun union_envs/2).

-spec guard_env(ast:guard()) -> {constr:constr_env(), safe | unsafe}.
guard_env(Guards) ->
    combine_guard_result(Guards, fun guard_test_env/1, fun intersect_envs/2).

-spec combine_guard_result(list(G),
                           fun((G) -> {constr:constr_env(), safe | unsafe}),
                           fun((constr:constr_env(), constr:constr_env()) ->
                                      constr:constr_env())) ->
          {constr:constr_env(), safe | unsafe}.
combine_guard_result(Guards, RecFun, CombineFun) ->
    lists:foldl(fun({Env, Status}, {AccEnv, AccStatus}) ->
                        {CombineFun(Env, AccEnv), merge_status(Status, AccStatus)}
                end,
                {#{}, safe},
                lists:map(RecFun, Guards)).

-spec guard_test_env(ast:guard_test()) -> {constr:constr_env(), safe | unsafe}.
guard_test_env(G) ->
    Default = {#{}, unsafe},
    case G of
        {call, _L, FunExp, Args} ->
            % check whether first arg is a variable
            case Args of
                [Fst | Rest] ->
                    case Fst of
                        {var, _, {local_ref, X}} -> var_test_env(FunExp, X, Rest);
                        _ -> Default
                    end;
                _ -> Default
            end;
        {op, _L, Op, Left, Right} ->
            if
                (Op =:= 'andalso') orelse (Op =:= 'and') ->
                    {EnvLeft, StatusLeft} = guard_test_env(Left),
                    {EnvRight, StatusRight} = guard_test_env(Right),
                    {intersect_envs(EnvLeft, EnvRight), merge_status(StatusLeft, StatusRight)};
                (Op =:= 'orelse') orelse (Op =:= 'or') ->
                    {EnvLeft, StatusLeft} = guard_test_env(Left),
                    {EnvRight, StatusRight} = guard_test_env(Right),
                    {union_envs(EnvLeft, EnvRight), merge_status(StatusLeft, StatusRight)};
                true -> Default
            end;
        {op, _L, 'not', Exp} ->
            {Env, Status} = guard_test_env(Exp),
            {negate_env(Env), Status};
        _ -> Default
    end.

merge_status(safe, safe) -> safe;
merge_status(_, _) -> unsafe.

% {var,{loc,"test_files/tycheck_simple.erl",202,16},{qref,erlang,is_integer,1}} for {'Y',0} and args []: {#{},unsafe}
-spec var_test_env(ast:guard_test(), ast:local_varname(), [ast:guard_test()]) ->
          {constr:constr_env(), safe | unsafe}.
var_test_env(FunExp, X, RestArgs) ->
    Default = {#{}, unsafe},
    XRef = {local_ref, X},
    Env =
        case FunExp of
            {var, _, Ref} ->
                case
                    case Ref of
                        {ref, A, B} -> {A, B};
                        {qref, erlang, A, B} -> {A, B};
                        _ -> unsupported
                    end
                of
                    unsupported -> Default;
                    {is_record, Arity} ->
                        % check whether first rest arg is an atom (the record name)
                        if
                            Arity =:= 2 orelse Arity =:= 3 ->
                                case RestArgs of
                                    [{'atom', _, RecordName} | _] ->
                                        #{XRef => {record, RecordName, []}};
                                    _ -> Default
                                end;
                            true -> Default
                        end;
                    {is_function, 2} ->
                        case RestArgs of
                            [{'integer', _, N}] ->
                                % The top type for functions with arity N
                                TopFunTy = {fun_full, utils:replicate(N, {predef, any}), {predef, none}},
                                #{XRef => TopFunTy};
                            _ -> Default
                        end;
                    {Name, 1} ->
                        case Name of
                            is_atom -> {#{XRef => {predef, atom}}, safe};
                            is_binary -> {#{XRef => {predef_alias, binary}}, safe};
                            is_bitstring -> {#{XRef => {predef_alias, bitstring}}, safe};
                            is_function -> {#{XRef => {predef_alias, function}}, safe};
                            is_integer -> {#{XRef => {predef, integer}}, safe};
                            is_float -> {#{XRef => {predef, float}}, safe};
                            is_list -> {#{XRef => {predef_alias, list}}, safe};
                            is_map -> {#{XRef => {predef_alias, map}}, safe};
                            is_number -> {#{XRef => {predef_alias, number}}, safe};
                            is_pid -> {#{XRef => {predef, pid}}, safe};
                            is_port -> {#{XRef => {predef, port}}, safe};
                            is_reference -> {#{XRef => {predef, reference}}, safe};
                            is_tuple -> #{XRef => {tuple_any}};
                            _ ->
                                case string:prefix(atom_to_list(Name), "is_") of
                                    nomatch -> ok;
                                    _ -> ?LOG_INFO("Unsupported type test ~w", Name)
                                end,
                                Default
                        end
                end;
            _ ->
                Default
        end,
    ?LOG_TRACE("Env resulting from var test ~200p for ~w and args ~200p: ~w", FunExp, X, RestArgs, Env),
    Env.


% f(p11, p12, ..., p1n) -> e1;
% ...
% f(pm1, pm2, ..., pmn) -> em
%
% is transformed into
%
% case {X1, ..., Xn} of
%   (p11, p12, ..., p1n) -> e1;
%   ...
%   (pm1, pm2, ..., pmn) -> em
% end
-spec fun_clauses_to_exp(ctx(), ast:loc(), [ast:fun_clauses()]) -> {[ast:local_varname()], ast:exp()}.
fun_clauses_to_exp(Ctx, L, FunClauses) ->
    Arity =
        case FunClauses of
            [] -> errors:ty_error(L, "expected function clauses");
            [{fun_clause, _, FirstPats, _, _} | Rest] ->
                lists:foldl(
                  fun({fun_clause, ThisLoc, ThisPats, _, _}, Arity) ->
                          if
                              length(ThisPats) =:= Arity -> Arity;
                              true -> errors:ty_error(ThisLoc,
                                                      "expected ~w arguments, but given ~w",
                                                      [Arity, length(ThisPats)])
                          end
                  end,
                  length(FirstPats),
                  Rest)
        end,
    Vars = fresh_vars(Ctx, Arity),
    ScrutExp = {tuple, L, lists:map(fun(V) -> {var, L, {local_ref, V}} end, Vars)},
    CaseClauses = lists:map(fun fun_clause_to_case_clause/1, FunClauses),
    {Vars, {'case', L, ScrutExp, CaseClauses}}.

-spec fun_clause_to_case_clause(ast:fun_clause()) -> ast:case_clause().
fun_clause_to_case_clause({fun_clause, L, Pats, Guards, Exps}) ->
    {case_clause, L, {tuple, L, Pats}, Guards, Exps}.

% if g1 -> e1;
%    ...
%    gn -> en
% end
%
% is transformed to
%
% case {}
%   _ when g1 -> e1;
%   ...
%   _ when gn -> en
% end
-spec if_exp_to_case_exp(ast:if_exp()) -> ast:case_exp().
if_exp_to_case_exp({'if', L, IfClauses}) ->
    ScrutExp = {tuple, L, []},
    Pat = {wildcard, L},
    CaseClauses =
        lists:map(fun({if_clause, ClauseLoc, Guards, Body}) ->
                          {case_clause, ClauseLoc, Pat, Guards, Body}
                  end, IfClauses),
    {'case', L, ScrutExp, CaseClauses}.

-spec sanity_check(const:constrs(), ast_spec:ty_map()) -> ok.
sanity_check(Cs, Spec) ->
    case ast_check:check_against_type(Spec, constr, constrs, Cs) of
        true ->
            ok;
        false ->
            ?ABORT("~s", "Invalid constraint generated")
    end.
