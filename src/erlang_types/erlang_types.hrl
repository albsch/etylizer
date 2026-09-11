-type type_descriptor() :: dnf_ty_variable:type().
-type variable() :: ty_variable:type().
-type monomorphic_variables() :: etally:monomorphic_variables().

%% keys of the emptiness cache: nodes, and the sub-problems of the tuple and
%% function decompositions (dnf_ty_tuple:phi/3, dnf_ty_function:phi/4)
-type is_empty_memo_key() :: ty_node:type()
    | {phi_tuple_memo, [ty_node:type()], [ty_tuple:type()]}
    | {phi_fun_memo, ty_node:type(), ty_node:type(), [ty_function:type()]}.
%% memo: the coinductive assumptions and the emptiness verdicts reached under
%% them, rolled back when an enclosing type turns out non-empty; facts: the
%% non-emptiness verdicts, which never rest on an assumption and are kept.
-record(is_empty_cache, {
    memo = #{} :: #{is_empty_memo_key() => boolean()},
    facts = #{} :: #{is_empty_memo_key() => false}
}).
-type is_empty_cache() :: #is_empty_cache{}.
-type normalize_cache() :: #{
    {ty_node:type(), monomorphic_variables()} => constraint_set:set_of_constraint_sets(),
    %% dnf_ty_tuple:phi_norm/4 stashes a sub-problem memo in the same threaded
    %% map, keyed by its (BigS, NegList) pair under a distinguishing tag.
    {phi_norm_tuple_memo, [ty_node:type()], [ty_tuple:type()]} => constraint_set:set_of_constraint_sets()
}.
-type all_variables_cache() :: #{ty_node:type() => _}.
-type unparse_cache() :: #{ty_node:type() => ast_ty()}.

-type ast_ty() :: ast:ty().
-type ast_mu_var() :: ast:ty_mu_var().
