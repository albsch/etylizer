-ifndef(METRICS_HRL).
-define(METRICS_HRL, true).

-ifdef(ety_metrics).
-define(METRIC(Category, Expr), metrics:record(Category, Expr)).
-define(METRIC_SET_FUN(Label), erlang:put(ety_cur_fun, Label)).
-define(METRIC_GET_FUN(), erlang:get(ety_cur_fun)).
-define(METRIC_FUN(), metrics:current_fun()).
-define(METRIC_INFER_FUN(FileName), metrics:inference_fun(FileName)).
%% Evaluate Expr only in metric builds. Used when the work itself
%% (iteration, multi-statement recording) must vanish without metrics.
-define(METRIC_DO(Expr), Expr).
-define(METRIC_ENGINE_CALL(), metrics:engine_call()).
-define(METRIC_MISS(), metrics:miss()).
-define(METRIC_WORK_START(Var), Var = metrics:work()).
-define(METRIC_WORK(Category, Label, Start), metrics:record_work(Category, Label, Start)).
%% A solved tally problem: one is_satisfiable partition, identified by its
%% constraint list so the same problem can be paired across two engines and
%% compared pairwise. Start is a ?METRIC_WORK_START reading taken before it.
-define(METRIC_PROBLEM(Constraints, Answer, Start), metrics:record_problem(Constraints, Answer, Start)).
-else.
-define(METRIC(Category, Expr), ok).
-define(METRIC_SET_FUN(Label), ok).
-define(METRIC_GET_FUN(), undefined).
-define(METRIC_FUN(), '__no_fun__').
-define(METRIC_INFER_FUN(_FileName), '__no_fun__').
-define(METRIC_DO(_Expr), ok).
-define(METRIC_ENGINE_CALL(), ok).
-define(METRIC_MISS(), ok).
-define(METRIC_WORK_START(_Var), ok).
-define(METRIC_WORK(_Category, _Label, _Start), ok).
-define(METRIC_PROBLEM(_Constraints, _Answer, _Start), ok).
-endif.

-endif.
