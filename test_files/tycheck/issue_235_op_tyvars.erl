-module(issue_235_op_tyvars).

-compile(export_all).
-compile(nowarn_export_all).

% Regression test for issue #235: the polymorphic type variables of the builtin
% operator schemes (andalso/orelse and the comparison operators) must be freshened
% at every use site. Before the fix these schemes were built with an empty binder
% (tyscm/1), so the variable leaked as a single shared free variable and two uses
% in one function got conflated into one unsatisfiable constraint set.

% The exact example from the issue.
-spec same() -> boolean().
same() ->
  true andalso true =/= ok.

% Two uses of andalso that must be instantiated at DIFFERENT result types.
% (true andalso 1) : 1 and (true andalso hello) : hello. With a shared,
% unfreshened variable these get conflated and the function fails to typecheck.
-spec two_andalso() -> {1, hello}.
two_andalso() ->
    X = true andalso 1,
    Y = true andalso hello,
    {X, Y}.

% Same for orelse: (false orelse 1) : 1 and (false orelse hello) : hello.
-spec two_orelse() -> {1, hello}.
two_orelse() ->
    X = false orelse 1,
    Y = false orelse hello,
    {X, Y}.
