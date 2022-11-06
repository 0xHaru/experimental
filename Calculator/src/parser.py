from __future__ import annotations

from enum import Enum

from lexer import Token


class ASTNode:
    def eval(self) -> float:
        pass


class BinaryExpr(ASTNode):
    class Op(Enum):
        SUM = 1
        SUB = 2
        MUL = 3
        DIV = 4

        @staticmethod
        def match(type: Token.Type) -> BinaryExpr.Op:
            match type:
                case Token.Type.PLUS:
                    return BinaryExpr.Op.SUM
                case Token.Type.MINUS:
                    return BinaryExpr.Op.SUB
                case Token.Type.STAR:
                    return BinaryExpr.Op.MUL
                case Token.Type.SLASH:
                    return BinaryExpr.Op.DIV
                case _:
                    raise Exception("Invalid token type")

    def __init__(self, operator: BinaryExpr.Op, left: ASTNode, right: ASTNode) -> None:
        self.operator = operator
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        operator = str(self.operator).split(".")[1]
        return f"({self.left} {operator} {self.right})"

    def eval(self) -> float:
        match self.operator:
            case BinaryExpr.Op.SUM:
                return self.left.eval() + self.right.eval()
            case BinaryExpr.Op.SUB:
                return self.left.eval() - self.right.eval()
            case BinaryExpr.Op.MUL:
                return self.left.eval() * self.right.eval()
            case BinaryExpr.Op.DIV:
                return self.left.eval() / self.right.eval()
            case _:
                raise Exception("Invalid node type")


class Literal(ASTNode):
    def __init__(self, value: float) -> None:
        self.value = value

    def __repr__(self) -> str:
        return str(self.value)

    def eval(self) -> float:
        return self.value


# Grammar:
#   E -> T | T + T | T - T
#   T -> F | F * F | F / F
#   F -> n | ( E )
class Parser:
    def __init__(self, tokens: list[Token]) -> None:
        self.tokens = tokens
        self.current = 0

    def peek(self) -> Token:
        return self.tokens[self.current]

    def is_at_end(self) -> bool:
        return self.tokens[self.current].type == Token.Type.EOL

    def advance(self) -> Token:
        if not self.is_at_end():
            self.current += 1
        return self.tokens[self.current - 1]

    def match(self, *types: Token.Type) -> bool:
        for type in types:
            if self.peek().type == type:
                return True
        return False

    def parse(self) -> ASTNode:
        return self.expr()

    def expr(self) -> ASTNode:
        # E -> T
        expr = self.term()

        # E -> T + T
        # E -> T - T
        while not self.is_at_end() and self.match(Token.Type.PLUS, Token.Type.MINUS):
            current_token = self.advance()
            operator = BinaryExpr.Op.match(current_token.type)
            right = self.term()
            expr = BinaryExpr(operator, left=expr, right=right)

        return expr

    def term(self) -> ASTNode:
        # T -> F
        expr = self.fact()

        # T -> F * F
        # T -> F / F
        while not self.is_at_end() and self.match(Token.Type.STAR, Token.Type.SLASH):
            current_token = self.advance()
            operator = BinaryExpr.Op.match(current_token.type)
            right = self.term()
            expr = BinaryExpr(operator, left=expr, right=right)

        return expr

    def fact(self) -> ASTNode:
        # F -> n
        if self.match(Token.Type.NUMBER):
            current_token = self.advance()
            return Literal(value=float(current_token.literal))

        # F -> ( E )
        if self.match(Token.Type.L_PAREN):
            self.advance()  # Consume L_PAREN
            expr = self.expr()

            if not self.match(Token.Type.R_PAREN):
                raise Exception("Syntax error: missing closing parenthesis")

            self.advance()  # Consume R_PAREN

            return expr

        raise Exception(f'Syntax error: "{self.peek().literal}"')
