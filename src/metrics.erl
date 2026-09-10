-module(metrics).

-export([
    init/0,
    record/2,
    dump/1,
    cleanup/0,
    current_fun/0,
    inference_fun/1,
    engine_call/0,
    miss/0,
    read_counters/0,
    work/0,
    work_since/1,
    record_work/3,
    record_problem/3
]).

-define(TABLE, ety_metrics_table).
% need persistent_term:get/2 to have a constant-time read without copying
-define(COUNTERS, ety_metrics_counters).
-define(IX_ENGINE_CALLS, 1).
-define(IX_MISSES, 2).

%% {EngineCalls, Misses, Reductions}, see work/0.
-type work() :: {non_neg_integer(), non_neg_integer(), non_neg_integer()}.

-spec init() -> ok.
init() ->
    ets:new(?TABLE, [named_table, duplicate_bag, public]),
    persistent_term:put(?COUNTERS, counters:new(2, [write_concurrency])),
    ok.

% Label of the function being checked, or '__no_fun__' outside one.
-spec current_fun() -> atom().
current_fun() ->
    case erlang:get(ety_cur_fun) of
        undefined -> '__no_fun__';
        Label -> Label
    end.

% Shaped like a function label so it cannot collide with a real one.
-spec inference_fun(file:filename()) -> atom().
inference_fun(FileName) ->
    list_to_atom(utils:sformat("~s:__inference__/0",
                               [filename:basename(filename:rootname(FileName))])).

% counters are global and monotonic
-spec engine_call() -> ok.
engine_call() -> bump(?IX_ENGINE_CALLS).

-spec miss() -> ok.
miss() -> bump(?IX_MISSES).

-spec bump(pos_integer()) -> ok.
bump(Index) ->
    case persistent_term:get(?COUNTERS, undefined) of
        undefined -> ok;
        Ref -> counters:add(Ref, Index, 1)
    end.

-spec read_counters() -> {non_neg_integer(), non_neg_integer()}.
read_counters() ->
    case persistent_term:get(?COUNTERS, undefined) of
        undefined -> {0, 0};
        Ref -> {counters:get(Ref, ?IX_ENGINE_CALLS), counters:get(Ref, ?IX_MISSES)}
    end.

% Use reductions of the BEAM as work proxy
-spec work() -> work().
work() ->
    {EngineCalls, Misses} = read_counters(),
    {Reductions, _SinceLast} = erlang:statistics(exact_reductions),
    {EngineCalls, Misses, Reductions}.

-spec work_since(work()) -> {integer(), integer(), integer()}.
work_since({Calls0, Misses0, Reductions0}) ->
    {Calls1, Misses1, Reductions1} = work(),
    {Calls1 - Calls0, Misses1 - Misses0, Reductions1 - Reductions0}.

%% Record the work done since Start as {Label, EngineCalls, Misses, Reductions}
%% under Category. Used through ?METRIC_WORK_START / ?METRIC_WORK.
-spec record_work(atom(), atom(), work()) -> ok.
record_work(Category, Label, Start) ->
    {EngineCalls, Misses, Reductions} = work_since(Start),
    record(Category, {Label, EngineCalls, Misses, Reductions}).

%% One solved tally problem: an is_satisfiable partition, identified by a hash
%% of its constraint list so the same problem can be found in the other
%% engine's run and compared pairwise. Recorded as
%%     tally_problem: {Fn, Key, Constraints, Answer, EngineCalls, Misses, Reductions}
%% over the span since Start (parsing the constraints and the search). A
%% partition whose worker is killed at the report timeout leaves no record,
%% deliberately: the report pairs what both engines finished and counts the
%% rest as the tail, instead of dropping whole functions.
-spec record_problem(list(), boolean(), work()) -> ok.
record_problem(Constraints, Answer, Start) ->
    {EngineCalls, Misses, Reductions} = work_since(Start),
    record(tally_problem, {current_fun(), erlang:phash2(Constraints, 16#100000000),
                           length(Constraints), Answer, EngineCalls, Misses, Reductions}).

-spec record(atom(), term()) -> ok.
record(Category, DataPoint) ->
    try
        ets:insert(?TABLE, {Category, DataPoint}),
        ok
    catch
        error:badarg -> ok
    end.

-spec dump(file:filename()) -> ok.
dump(Path) ->
    Entries = ets:tab2list(?TABLE),
    Grouped = lists:foldl(
        fun({Category, DataPoint}, Acc) ->
            maps:update_with(Category, fun(Old) -> [DataPoint | Old] end, [DataPoint], Acc)
        end,
        #{},
        Entries
    ),
    JsonMap = maps:fold(
        fun(Category, DataPoints, Acc) ->
            Acc#{atom_to_binary(Category, utf8) => lists:reverse([tuple_to_list(DP) || DP <- DataPoints])}
        end,
        #{},
        Grouped
    ),
    JsonBin = json:encode(JsonMap),
    ok = file:write_file(Path, JsonBin).

-spec cleanup() -> ok.
cleanup() ->
    _ = persistent_term:erase(?COUNTERS),
    try
        ets:delete(?TABLE),
        ok
    catch
        error:badarg -> ok
    end.
