-module(lexer).
-export([tokenize/1]).

is_digit(Ch) when Ch >= $0, Ch =< $9 -> true;
is_digit(_) -> false.

consume_number(Chars) -> consume_number(Chars, []).

consume_number([Ch | Tail], Acc) when Ch >= $0, Ch =< $9 -> consume_number(Tail, [Ch | Acc]);
consume_number(_, Acc) -> list_to_integer(lists:reverse(Acc)).

tokenize(Chars, Tokens) ->
    case Chars of
        []           -> lists:reverse(Tokens);
        [$+  | Tail] -> tokenize(Tail, [{op, add,  1}  | Tokens]);
        [$-  | Tail] -> tokenize(Tail, [{op, sub,  1}  | Tokens]);
        [$*  | Tail] -> tokenize(Tail, [{op, mul,  2}  | Tokens]);
        [$/  | Tail] -> tokenize(Tail, [{op, ddiv, 2}  | Tokens]);
        [$~  | Tail] -> tokenize(Tail, [{op, neg,  3}  | Tokens]);
        [$(  | Tail] -> tokenize(Tail, [{paren, left}  | Tokens]);
        [$)  | Tail] -> tokenize(Tail, [{paren, right} | Tokens]);
        [$\s | Tail] -> tokenize(Tail, Tokens);
        [$\t | Tail] -> tokenize(Tail, Tokens);
        [$\n | Tail] -> tokenize(Tail, Tokens);
        [Ch  | Tail] ->
            case is_digit(Ch) of
                true ->
                    Val = consume_number([Ch | Tail]),
                    tokenize(Tail, [{int, Val} | Tokens]);
                false ->
                    error("Unexpected character")
            end
    end.

tokenize(Source) -> tokenize(Source, []).
