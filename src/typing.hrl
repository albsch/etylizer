-record(ctx,
        { symtab :: symtab:t(),
          overlay_symtab :: symtab:t(),
          sanity :: t:opt(ast_check:ty_map())
        }).

-type ctx() :: #ctx{}.
