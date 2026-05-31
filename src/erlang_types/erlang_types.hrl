-type type_descriptor() :: dnf_ty_variable:type().
-type variable() :: ty_variable:type().
-type monomorphic_variables() :: etally:monomorphic_variables().

-type is_empty_cache() :: #{
    type_descriptor() => boolean(),
    % dnf_ty_tuple:phi/3 keeps its sub-problem memo in the same threaded map,
    % under a tag that cannot collide with the descriptor keys above.
    {phi_tuple_memo, [ty_node:type()], [ty_tuple:type()]} => boolean()
}.
-type normalize_cache() :: #{
    {ty_node:type(), monomorphic_variables()} => constraint_set:set_of_constraint_sets(),
    % dnf_ty_tuple:phi_norm/4 keeps its sub-problem memo in the same threaded
    % map, under a tag that cannot collide with the node keys above.
    {phi_norm_tuple_memo, [ty_node:type()], [ty_tuple:type()]} => constraint_set:set_of_constraint_sets()
}.
-type all_variables_cache() :: #{ty_node:type() => _}.
-type unparse_cache() :: #{ty_node:type() => ast_ty()}.

-type ast_ty() :: ast:ty().
-type ast_mu_var() :: ast:ty_mu_var().
