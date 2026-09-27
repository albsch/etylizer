-module(symtab_cache).

% Persistent cache of what etylizer derives from a source file and needs in
% every run, kept in <project root>/_etylizer/symtab_cache.
%
% Two things are cached. symtab:extend_symtab_with_module_list/4 adds the
% specs, types and records of every module the checked file refers to, and of
% everything those modules refer to through their types; what one module adds
% is a function of its source, the overlay, the gradual typing mode and
% etylizer's own parsing and symtab code, nothing else. stdtypes:builtin_funs/0
% derives the types of the builtin functions from OTP's erlang.erl. Both are
% computed once and reused by every later run, so the standard symtab (the
% erlang module and the OTP modules it pulls in), the per-module dependency
% symtabs and the builtin functions all come out of this one table.
%
% An entry is keyed by the source file and a tag chosen by the caller and
% holds the file's size and modification time, its hash and the value as a
% binary. A run loads the table when it starts (init/1) and writes it back
% once at the end (cleanup/0) if it gained entries. Without init/1 every
% lookup misses, so callers outside a run (tests, tooling) see the old
% behaviour.

-include("log.hrl").
-include("etylizer_main.hrl").
-include_lib("kernel/include/file.hrl").

-export([init/1, cleanup/0, save/0, cached/3, lookup/2, store/3]).

-define(TABLE, symtab_cache).
-define(META, symtab_cache_meta).
-define(VERSION, 2).

% A file modified within the last seconds is validated by its hash, since two
% edits can fall into the same second with the same size.
-define(SETTLE_SECONDS, 2).

% The code that computes a cached value: parsing, the AST transformation and
% the symtab construction. A change in any of these modules invalidates the
% whole file. Modules a build does not have are skipped.
-define(CODE_MODULES, [ast, ast_erl, ast_lib, ast_transform, ast_utils, attr, errors, ety_records,
                       feature_flags, parse, parse_beam, parse_cache, stdtypes, symtab, symtab_cache,
                       utils]).

-type stamp() :: {non_neg_integer(), non_neg_integer()}. % modification time, size

-spec init(#opts{}) -> ok.
init(Opts) ->
    case ets:whereis(?TABLE) of
        undefined -> ok;
        _ -> cleanup()
    end,
    case Opts#opts.sanity of
        true ->
            % --sanity checks the forms of every parsed file. A cached entry
            % skips that parse, so the cache stays off.
            ok;
        false ->
            ets:new(?TABLE, [set, named_table, public]),
            File = paths:symtab_cache_file_name(Opts),
            Code = code_hash(),
            ets:insert(?TABLE, {?META, File, Code, false}),
            load(File, Code)
    end.

-spec load(file:filename(), non_neg_integer()) -> ok.
load(File, Code) ->
    case file:read_file(File) of
        {ok, Bin} ->
            try binary_to_term(Bin) of
                {symtab_cache, ?VERSION, Code, Entries} when is_map(Entries) ->
                    ets:insert(?TABLE, maps:to_list(Entries)),
                    ?LOG_DEBUG("Loaded ~p cached entries from ~s", maps:size(Entries), File);
                {symtab_cache, ?VERSION, _, _} ->
                    ?LOG_DEBUG("Ignoring symtab cache ~s: etylizer code changed", File);
                _ ->
                    ?LOG_DEBUG("Ignoring symtab cache ~s: unknown format", File)
            catch _:_ ->
                ?LOG_DEBUG("Ignoring unreadable symtab cache ~s", File)
            end;
        {error, enoent} -> ok;
        {error, Reason} ->
            ?LOG_DEBUG("Cannot read symtab cache ~s: ~p", File, Reason)
    end.

% The value Compute derives from Filename, taken from the cache when the file
% still has the content the cached value was computed from.
-spec cached(file:filename(), term(), fun(() -> T)) -> T.
cached(Filename, Tag, Compute) ->
    case lookup(Filename, Tag) of
        {ok, Value} ->
            Value;
        miss ->
            Value = Compute(),
            store(Filename, Tag, Value),
            Value
    end.

-spec lookup(file:filename(), term()) -> {ok, term()} | miss.
lookup(Filename, Tag) ->
    case ets:whereis(?TABLE) of
        undefined -> miss;
        _ ->
            Key = {Filename, Tag},
            case ets:lookup(?TABLE, Key) of
                [{_, {Stamp, Hash, Bin}}] ->
                    case unchanged(Filename, Stamp, Hash) of
                        same ->
                            {ok, share_file_names(binary_to_term(Bin))};
                        {restamp, NewStamp} ->
                            ets:insert(?TABLE, {Key, {NewStamp, Hash, Bin}}),
                            mark_dirty(),
                            {ok, share_file_names(binary_to_term(Bin))};
                        changed ->
                            miss
                    end;
                _ -> miss
            end
    end.

% A file with the size and modification time it had when the entry was stored
% has the same content, unless it was modified just now; then, and when the
% stamp differs, the hash decides.
-spec unchanged(file:filename(), stamp(), string()) -> same | {restamp, stamp()} | changed.
unchanged(Filename, Stamp, Hash) ->
    Now = erlang:system_time(second),
    case stamp(Filename) of
        {ok, {MTime, _} = Stamp} when MTime < Now - ?SETTLE_SECONDS -> same;
        {ok, NewStamp} ->
            case utils:hash_file(Filename) of
                Hash when NewStamp =:= Stamp -> same;
                Hash -> {restamp, NewStamp};
                _ -> changed
            end;
        error -> changed
    end.

-spec stamp(file:filename()) -> {ok, stamp()} | error.
stamp(Filename) ->
    case file:read_file_info(Filename, [{time, posix}]) of
        {ok, #file_info{mtime = MTime, size = Size}} when is_integer(MTime), is_integer(Size) -> {ok, {MTime, Size}};
        _ -> error
    end.

-spec store(file:filename(), term(), term()) -> ok.
store(Filename, Tag, Value) ->
    case ets:whereis(?TABLE) of
        undefined -> ok;
        _ ->
            case {stamp(Filename), utils:hash_file(Filename)} of
                {{ok, Stamp}, Hash} when is_list(Hash) ->
                    Entry = {Stamp, Hash, term_to_binary(Value)},
                    ets:insert(?TABLE, {{Filename, Tag}, Entry}),
                    mark_dirty();
                _ -> ok
            end
    end.

-spec mark_dirty() -> ok.
mark_dirty() ->
    case ets:lookup(?TABLE, ?META) of
        [{?META, File, Code, false}] -> ets:insert(?TABLE, {?META, File, Code, true}), ok;
        _ -> ok
    end.

% Write the table back if it gained entries since it was loaded.
-spec save() -> ok.
save() ->
    case ets:whereis(?TABLE) of
        undefined -> ok;
        _ ->
            case ets:lookup(?TABLE, ?META) of
                [{?META, File, Code, true}] ->
                    Entries = maps:from_list([{K, V} || {K, V} <- ets:tab2list(?TABLE)]),
                    write(File, term_to_binary({symtab_cache, ?VERSION, Code, Entries})),
                    ets:insert(?TABLE, {?META, File, Code, false}),
                    ok;
                _ -> ok
            end
    end.

-spec write(file:filename(), binary()) -> ok.
write(File, Bin) ->
    % Write a private file and rename it into place, so a run that starts
    % while this one writes never reads a partial file.
    Tmp = File ++ "." ++ os:getpid() ++ ".tmp",
    Result =
        case filelib:ensure_dir(File) of
            ok ->
                case file:write_file(Tmp, Bin) of
                    ok -> file:rename(Tmp, File);
                    Err -> Err
                end;
            Err -> Err
        end,
    case Result of
        ok ->
            ?LOG_DEBUG("Wrote symtab cache ~s (~p bytes)", File, byte_size(Bin));
        {error, Reason} ->
            _ = file:delete(Tmp),
            ?LOG_WARN("Cannot write symtab cache ~s: ~p", File, Reason)
    end.

% binary_to_term returns a term without sharing: every location holds its own
% copy of the file name, which makes a symtab read from the cache three times
% the size of one built from the sources, and everything that copies or
% traverses the symtab per function pays for it. Share the file names again.
-spec share_file_names(T) -> T.
share_file_names(Value) ->
    {Shared, _} = share(Value, #{}),
    Shared.

-spec share(T, Seen) -> {T, Seen} when Seen :: #{string() => string()}.
share({loc, File, Line, Col}, Seen) when is_list(File) ->
    case Seen of
        #{File := Shared} -> {{loc, Shared, Line, Col}, Seen};
        _ -> {{loc, File, Line, Col}, Seen#{File => File}}
    end;
share(T, Seen) when is_tuple(T) ->
    {L, Seen1} = share_list(tuple_to_list(T), Seen),
    {list_to_tuple(L), Seen1};
share(L, Seen) when is_list(L) ->
    share_list(L, Seen);
share(M, Seen) when is_map(M) ->
    {L, Seen1} = share_list(maps:to_list(M), Seen),
    {maps:from_list(L), Seen1};
share(X, Seen) ->
    {X, Seen}.

-spec share_list(T, Seen) -> {T, Seen} when Seen :: #{string() => string()}.
share_list([H | T], Seen) ->
    {H1, Seen1} = share(H, Seen),
    {T1, Seen2} = share_list(T, Seen1),
    {[H1 | T1], Seen2};
share_list([], Seen) ->
    {[], Seen};
share_list(X, Seen) ->
    share(X, Seen).

-spec cleanup() -> ok.
cleanup() ->
    save(),
    case ets:whereis(?TABLE) of
        undefined -> ok;
        _ -> ets:delete(?TABLE), ok
    end.

% Identifies the code that computes the cached values and the runtime that
% parses the sources.
-spec code_hash() -> non_neg_integer().
code_hash() ->
    Md5s = [{M, M:module_info(md5)} || M <- ?CODE_MODULES, code:ensure_loaded(M) =:= {module, M}],
    erlang:phash2({Md5s, erlang:system_info(otp_release), erlang:system_info(version)}).
