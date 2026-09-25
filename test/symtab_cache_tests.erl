-module(symtab_cache_tests).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

with_project(Fun) ->
    tmp:with_tmp_dir("symtab_cache", "test", delete, fun(Dir) ->
        Src = filename:join(Dir, "m.erl"),
        ok = file:write_file(Src, "-module(m).\n"),
        Fun(Dir, Src, #opts{project_root = Dir})
    end).

cache_file(Dir) -> filename:join([Dir, "_etylizer", "symtab_cache"]).

tab() ->
    Loc = fun(Line) -> {loc, "src/m.erl", Line, 1} end,
    symtab:from_types([{{ty_key, m, t, 0}, {ty_scheme, [], {predef, any}}},
                       {{ty_key, m, u, 0}, {ty_scheme, [], {named, Loc(3), {ty_ref, m, t, 0}, []}}},
                       {{ty_key, m, v, 0}, {ty_scheme, [], {named, Loc(4), {ty_ref, m, t, 0}, []}}}]).

roundtrip_test() ->
    with_project(fun(Dir, Src, Opts) ->
        ok = symtab_cache:init(Opts),
        miss = symtab_cache:lookup(Src, {m, dynamic, "ov-a"}),
        ok = symtab_cache:store(Src, {m, dynamic, "ov-a"}, {tab(), [lists]}),
        {ok, {T, [lists]}} = symtab_cache:lookup(Src, {m, dynamic, "ov-a"}),
        ?assertEqual(tab(), T),
        % another tag is another entry
        miss = symtab_cache:lookup(Src, {m, dynamic, "ov-b"}),
        miss = symtab_cache:lookup(Src, {m, infer, "ov-a"}),
        ok = symtab_cache:cleanup(),
        ?assert(filelib:is_file(cache_file(Dir))),
        % the next run reads it back, with the file names shared again
        ok = symtab_cache:init(Opts),
        {ok, {T2, [lists]}} = symtab_cache:lookup(Src, {m, dynamic, "ov-a"}),
        ?assertEqual(tab(), T2),
        ?assert(erts_debug:size(T2) < erts_debug:flat_size(T2)),
        ok = symtab_cache:cleanup()
    end).

cached_computes_once_test() ->
    with_project(fun(_Dir, Src, Opts) ->
        ok = symtab_cache:init(Opts),
        Compute = fun() -> erlang:put(computed, erlang:get(computed) + 1), [{f, 1, spec}] end,
        erlang:put(computed, 0),
        [{f, 1, spec}] = symtab_cache:cached(Src, builtin_funs, Compute),
        [{f, 1, spec}] = symtab_cache:cached(Src, builtin_funs, Compute),
        ?assertEqual(1, erlang:get(computed)),
        ok = symtab_cache:cleanup(),
        ok = symtab_cache:init(Opts),
        [{f, 1, spec}] = symtab_cache:cached(Src, builtin_funs, Compute),
        ?assertEqual(1, erlang:get(computed)),
        ok = symtab_cache:cleanup()
    end).

changed_source_test() ->
    with_project(fun(_Dir, Src, Opts) ->
        ok = symtab_cache:init(Opts),
        ok = symtab_cache:store(Src, m, tab()),
        ok = symtab_cache:cleanup(),
        ok = file:write_file(Src, "-module(m).\n-export([f/0]).\n"),
        ok = symtab_cache:init(Opts),
        miss = symtab_cache:lookup(Src, m),
        ok = symtab_cache:cleanup()
    end).

% Same content written again: the stamp may differ, the hash decides.
touched_source_test() ->
    with_project(fun(_Dir, Src, Opts) ->
        ok = symtab_cache:init(Opts),
        ok = symtab_cache:store(Src, m, tab()),
        ok = symtab_cache:cleanup(),
        {ok, Content} = file:read_file(Src),
        ok = file:write_file(Src, Content),
        ok = file:change_time(Src, {{2020, 1, 1}, {0, 0, 0}}),
        ok = symtab_cache:init(Opts),
        {ok, T} = symtab_cache:lookup(Src, m),
        ?assertEqual(tab(), T),
        ok = symtab_cache:cleanup()
    end).

missing_source_test() ->
    with_project(fun(Dir, _Src, Opts) ->
        Missing = filename:join(Dir, "gone.erl"),
        ok = symtab_cache:init(Opts),
        ok = symtab_cache:store(Missing, gone, tab()),
        miss = symtab_cache:lookup(Missing, gone),
        ok = symtab_cache:cleanup()
    end).

unreadable_cache_file_test() ->
    with_project(fun(Dir, Src, Opts) ->
        ok = filelib:ensure_dir(cache_file(Dir)),
        ok = file:write_file(cache_file(Dir), <<"not a cache">>),
        ok = symtab_cache:init(Opts),
        miss = symtab_cache:lookup(Src, m),
        ok = symtab_cache:store(Src, m, tab()),
        ok = symtab_cache:cleanup(),
        ok = symtab_cache:init(Opts),
        {ok, _} = symtab_cache:lookup(Src, m),
        ok = symtab_cache:cleanup()
    end).

not_initialized_test() ->
    with_project(fun(Dir, Src, _Opts) ->
        miss = symtab_cache:lookup(Src, m),
        ok = symtab_cache:store(Src, m, tab()),
        ok = symtab_cache:cleanup(),
        ?assertNot(filelib:is_file(cache_file(Dir)))
    end).

sanity_disables_test() ->
    with_project(fun(Dir, Src, Opts) ->
        ok = symtab_cache:init(Opts#opts{sanity = true}),
        ok = symtab_cache:store(Src, m, tab()),
        miss = symtab_cache:lookup(Src, m),
        ok = symtab_cache:cleanup(),
        ?assertNot(filelib:is_file(cache_file(Dir)))
    end).

% A symtab built from the cache equals the one built from the sources.
cached_symtab_test_() ->
    {timeout, 60, fun() ->
        with_project(fun(_Dir, _Src, Opts) ->
            SearchPath = paths:compute_search_path(Opts),
            Overlay = symtab:empty(),
            Build = fun() ->
                symtab:extend_symtab_with_module_list(symtab:empty(), SearchPath, [calendar], Overlay)
            end,
            parse_cache:with_cache(Opts, fun() ->
                ok = symtab_cache:init(Opts),
                Fresh = Build(),
                ok = symtab_cache:cleanup(),
                ok = symtab_cache:init(Opts),
                {_, File, _} = paths:find_module_path(SearchPath, calendar),
                {ok, _} = symtab_cache:lookup(File, {calendar, dynamic, symtab:overlay_id(Overlay)}),
                Cached = Build(),
                ok = symtab_cache:cleanup(),
                ?assertEqual(Fresh, Cached)
            end)
        end)
    end}.
