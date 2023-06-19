-module(eq).

% data structures which implement equality should provide an efficient hashing function

% should be parameterized over X
-type x() :: term().
-type hash() :: integer().

-callback equal(x(), x()) -> boolean().
-callback compare(x(), x()) -> -1 | 0 | 1.
-callback hash(x()) -> hash().
