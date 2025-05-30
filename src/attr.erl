-module(attr).

% @doc Parser for -etylizer attributes

-export([
    parse_ety_attr/2,
    ety_attrs_from_file/1
   ]).
    
-type ety_attr() :: {etylizer, ast:loc(), term()}.

-spec ety_attrs_from_file(file:filename()) -> t:opt([ety_attr()], string()).
ety_attrs_from_file(Path) ->
    case utils:file_get_lines(Path) of
        {ok, Lines} -> ety_attrs_from_lines(Path, Lines);
        {error, Why} -> {error, utils:sformat("Error reading file ~s: ~1000p", Path, Why)}
    end.

-spec ety_attrs_from_lines(string(), [string()]) -> t:opt([ety_attr()], string()).
ety_attrs_from_lines(Path, Lines) -> ety_attrs_from_lines(Path, 1, Lines).

-spec ety_attrs_from_lines(string(), t:lineno(), [string()]) -> t:opt([ety_attr()], string()).
ety_attrs_from_lines(Path, Lineno, Lines) ->
    Loop =
        fun Loop(N, List) ->
            case List of
                [] -> [];
                [Line | RestLines] ->
                    Rest = Loop(N + 1, RestLines),
                    case parse_ety_attr({loc, Path, N, 1}, Line) of
                        no_attr -> Rest;
                        {ok, R} -> [R | Rest]
                    end
            end
        end,
    try {ok, Loop(Lineno, Lines)}
    catch {bad_attr, Msg} -> {error, utils:sformat("~1000p", Msg)} end.

-spec parse_ety_attr(ast:loc(), string()) -> no_attr | {ok, ety_attr()}.
parse_ety_attr(Loc, S) ->
    {loc, _, N, _} = Loc,
    case S of
       "%-etylizer" ++ Rest ->
           case string:trim(Rest) of
               TermStr = ("(" ++ _) ->
                   case erl_scan:string(TermStr, N) of
                       {ok, Toks, _} ->
                           case erl_parse:parse_term(Toks) of
                               {ok, Term} -> {ok, {etylizer, Loc, Term}};
                               {error, E} -> throw({bad_attr, E})
                            end;
                        E -> throw({bad_attr, E})
                    end;
                _ -> throw({bad_attr, "Invalid etylizer attribute"})
            end;
        _ -> no_attr
    end.
