-module(type).

% should be parameterized over X
-type x() :: term(). 

-callback is_any(x()) -> boolean().
-callback is_empty(x()) -> boolean().

-callback empty() -> x().
-callback any() -> x().

-callback union(X, X) -> X when X :: x().
-callback intersect(X, X) -> X when X :: x().
-callback diff(X, X) -> X when X :: x().
-callback negate(X) -> X when X :: x().
