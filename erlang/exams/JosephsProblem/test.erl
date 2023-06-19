-module(test).
-export([test/0]).

test() ->
    joseph:joseph(30, 3),       % Joseph is the Hebrew in position 29
    joseph:joseph(300, 1001),   % Joseph is the Hebrew in position 226
    joseph:joseph(3000, 37),    % Joseph is the Hebrew in position 1182
    joseph:joseph(26212, 2025), % Joseph is the Hebrew in position 20593
    joseph:joseph(1000, 1000),  % Joseph is the Hebrew in position 609
    joseph:joseph(2345, 26212), % Joseph is the Hebrew in position 1896
    joseph:joseph(100000, 7).   % Joseph is the Hebrew in position 27152
