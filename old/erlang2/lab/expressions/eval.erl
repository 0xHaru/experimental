-module(eval).
-export([eval/1]).

evalRPN(RPNExpr) -> hd(lists:foldl(fun evalRPN/2, [], RPNExpr)).

evalRPN({op, add,  _},  [A, B | T]) -> [B + A | T];
evalRPN({op, sub,  _},  [A, B | T]) -> [B - A | T];
evalRPN({op, mul,  _},  [A, B | T]) -> [B * A | T];
evalRPN({op, ddiv,  _}, [A, B | T]) -> [B / A | T];
evalRPN({op, neg,  _},  [A | T])    -> [-A | T];
evalRPN({int, Val},     Stack)      -> [Val | Stack].

eval(Expr) ->
    Tokens = lexer:tokenize(Expr),
    RPNExpr = parser:parse(Tokens),
    evalRPN(RPNExpr).

