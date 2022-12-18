-module(parser).
-export([parse/1]).

% Reference: https://en.wikipedia.org/wiki/Shunting_yard_algorithm

% Number:
%   put it into the output queue
parse([{int, Val} | TokensT], OpStack, OutQ) ->
    parse(TokensT, OpStack, OutQ ++ [{int, Val}]);

% Binary operator WHEN TokenPrec <= StackPrec :
%   - pop the head off the stack and put it into the output queue
%   - push the token onto the operator stack
%
% Note: I don't need to check that O1 is left-associative because all the supported
%       operators are left-associative
parse([{op, TokenOp, TokenPrec} | TokensT],
      [{op, StackOp, StackPrec} | StackT],
      OutQ)
    when TokenPrec =< StackPrec
->
    parse(TokensT,
          [{op, TokenOp, TokenPrec} | StackT],
          OutQ ++ [{op, StackOp, StackPrec}]);

% Binary operator WHEN TokenPrec > StackPrec :
%   push the token onto the operator stack
parse([{op, TokenOp, TokenPrec} | TokensT],
      [{op, StackOp, StackPrec} | StackT],
      OutQ)
    when TokenPrec > StackPrec
->
    parse(TokensT,
          [{op, TokenOp, TokenPrec}, {op, StackOp, StackPrec} | StackT],
          OutQ);

% Binary operator WHEN OpStack is empty :
%   push the token onto the operator stack
parse([{op, TokenOp, TokenPrec} | TokensT],
      OpStack,
      OutQ)
->
    parse(TokensT,
          [{op, TokenOp, TokenPrec} | OpStack],
          OutQ);

% Left parenthesis:
%   push the token onto the operator stack
parse([{paren, left} | TokensT], OpStack, OutQ) ->
    parse(TokensT, [{paren, left} | OpStack], OutQ);

% Right parenthesis:
%   pop the operator stack until there is a left parenthesis at the top of the operator stack
parse([{paren, right} | TokensT], OpStack, OutQ) ->
    {NewTokens, NewOpStack, NewOutQ} = pop_until_l_paren(TokensT, OpStack,  OutQ),
    parse(NewTokens, NewOpStack, NewOutQ);

% Empty tokens:
%   pop every operator from the operator stack and put them onto the output queue
parse([], [StackH | StackT], OutQ) -> parse([], StackT, OutQ ++ [StackH]);

% Empty tokens and empty operator stack:
%   return the output queue
parse([], [], OutQ) -> OutQ.

pop_until_l_paren(Tokens, [{paren,left} | StackT], OutQ) -> {Tokens, StackT, OutQ};

pop_until_l_paren(Tokens, [StackH | StackT], OutQ) ->
    pop_until_l_paren(Tokens, StackT, OutQ ++ [StackH]).

% Infix Notation -> Reverse Polish Notation
% 1 + 2 * 3 -> 1 2 3 * +
parse(Tokens) -> parse(Tokens, [], []).
