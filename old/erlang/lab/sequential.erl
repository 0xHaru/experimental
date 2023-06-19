-module(sequential).
-export([is_palindrome/1, is_an_anagram/2, factors/1, factors_tr/1, is_proper/1]).

% 1.
is_letter(Ch) when Ch >= $a, Ch =< $z -> true;
is_letter(Ch) when Ch >= $A, Ch =< $Z -> true;
is_letter(_) -> false.

is_palindrome(Str) ->
    LC = string:lowercase(Str),
    Letters = lists:filter(fun is_letter/1, LC),
    Letters =:= lists:reverse(Letters).

% sequential:is_palindrome("detartrated").        -> true
% sequential:is_palindrome("Do geese see God?").  -> true
% sequential:is_palindrome("Rise to vote, sir."). -> true
% sequential:is_palindrome("This is a test").     -> false

% 2.
is_an_anagram(Str, Lst) ->
    SortedStr = lists:sort(Str),
    SortedStrings = lists:map(fun lists:sort/1, Lst),
    lists:member(SortedStr, SortedStrings).

% sequential:is_an_anagram("restful", ["functional", "programming", "fluster"]). -> true
% sequential:is_an_anagram("restful", ["functional", "programming", "cluster"]). -> false

% 3.
factors(Num) -> factors(Num, 2).

factors(1, _) -> [];
factors(Num, Fact) when Num rem Fact =:= 0 -> [Fact | factors(Num div Fact, Fact)];
factors(Num, Fact) -> factors(Num, Fact + 1).

% sequential:factors(60). -> [2,2,3,5]

% Tail-recursive version
factors_tr(1) -> [];
factors_tr(Num) -> factors_tr(Num, 2, []).

factors_tr(1, _, Acc) -> lists:reverse(Acc);
factors_tr(Num, Fact, Acc) when Num rem Fact =:= 0 -> factors_tr(Num div Fact, Fact, [Fact | Acc]);
factors_tr(Num, Fact, Acc) -> factors_tr(Num, Fact + 1, Acc).

% sequential:factors_tr(60). -> [2,2,3,5]

% 4.
is_proper(Num) ->
    Divisors = [N || N <- lists:seq(1, Num div 2), Num rem N =:= 0],
    lists:foldl(fun(X, Y) -> X + Y end, 0, Divisors) =:= Num.

% sequential:is_proper(6). -> true
