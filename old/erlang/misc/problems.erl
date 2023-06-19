% https://purijatin.github.io/newsletters/erlang-99/

-module(problems).

-compile(export_all).

% 1. Find the last element of a list
%    problems:last([1,2,3]) -> 3
last([H]) ->
    H;
last([_ | T]) ->
    last(T).

% 2. Find the last but one element of a list
%    problems:last([1,2,3]) -> 2
penultimate([H, _]) ->
    H;
penultimate([_ | T]) ->
    penultimate(T).

% 3. Find the Kth element of a list
%    problems:kth([1,2,3],2) -> 3
kth([H | _], 0) ->
    H;
kth([_ | T], K) ->
    kth(T, K - 1).

% 4. Find the number of elements of a list
%    problems:len([1,2,3]) -> 3
len(L) ->
    len(L, 0).

len([], Acc) ->
    Acc;
len([_ | T], Acc) ->
    len(T, Acc + 1).

% 5. Reverse a list
%    problems:reverse([1,2,3]) -> [3,2,1]
reverse(L) ->
    reverse(L, []).

reverse([], Acc) ->
    Acc;
reverse([H | T], Acc) ->
    reverse(T, [H | Acc]).

% 6. Find out whether a list is a palindrome
%    problems:is_palindrome([1,2,3,2,1]) -> true
is_palindrome(L) ->
    L == reverse(L).

% 7. Flatten a nested list structure
%    problems:flatten([1,2,[3,[4,[5,6]]]]) -> [1,2,3,4,5,6]

% Easier solution but less efficient
flatten(X) ->
    lists:reverse(flatten(X, [])).

flatten([], Acc) ->
    Acc;
flatten([H | T], Acc) when is_list(H) ->
    flatten(T, flatten(H, Acc));
flatten([H | T], Acc) ->
    flatten(T, [H | Acc]).

% Optimized solution
flatten_opt(L) ->
    flatten_opt(L, []).

flatten_opt([H | T], Tail) ->
    flatten_opt(H, flatten_opt(T, Tail));
flatten_opt([], Tail) ->
    Tail;
flatten_opt(Element, Tail) ->
    % io:format("~p~n", [Element]),
    [Element | Tail].
