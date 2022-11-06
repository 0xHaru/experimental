from __future__ import annotations

from enum import Enum


class Token:
    class Type(Enum):
        NUMBER = 1

        PLUS = 2
        MINUS = 3
        STAR = 4
        SLASH = 5
        L_PAREN = 6
        R_PAREN = 7

        EOL = 8

    def __init__(self, type: Token.Type, literal: str) -> None:
        self.type = type
        self.literal = literal

    def __repr__(self) -> str:
        type = str(self.type).split(".")[1]

        if self.type == Token.Type.NUMBER:
            return f"{type}={self.literal}"

        return type


class Lexer:
    def __init__(self, source: str) -> None:
        self.source = source
        self.tokens: list[Token] = []
        self.start = 0
        self.current = 0

    def is_at_end(self) -> bool:
        return self.current >= len(self.source)

    def is_digit(self, char: str) -> bool:
        return char in "0123456789"

    def peek(self) -> str:
        if self.is_at_end():
            return "\0"
        return self.source[self.current]

    def peek_next(self) -> str:
        if self.current + 1 >= len(self.source):
            return "\0"
        return self.source[self.current + 1]

    def advance(self) -> str:
        self.current += 1
        return self.source[self.current - 1]

    def add_token(self, type: Token.Type, literal: str) -> None:
        self.tokens.append(Token(type, literal))

    def consume_number(self) -> None:
        while self.is_digit(self.peek()):
            self.advance()

        if self.peek() == "." and self.is_digit(self.peek_next()):
            self.advance()

        while self.is_digit(self.peek()):
            self.advance()

    def scan_token(self) -> None:
        char = self.advance()
        literal = self.source[self.start : self.current]

        match char:
            case "+":
                self.add_token(Token.Type.PLUS, literal)
            case "-":
                self.add_token(Token.Type.MINUS, literal)
            case "*":
                self.add_token(Token.Type.STAR, literal)
            case "/":
                self.add_token(Token.Type.SLASH, literal)
            case "(":
                self.add_token(Token.Type.L_PAREN, literal)
            case ")":
                self.add_token(Token.Type.R_PAREN, literal)
            # Ignore whitespace
            case " ":
                return
            case "\t":
                return
            case "\n":
                return
            case _:
                if not self.is_digit(char):
                    raise Exception(f'Lexical error: "{self.source[self.current - 1]}"')

                self.consume_number()
                literal = self.source[self.start : self.current]
                self.add_token(Token.Type.NUMBER, literal)

    def tokenize(self) -> list[Token]:
        while not self.is_at_end():
            self.start = self.current
            self.scan_token()

        self.add_token(Token.Type.EOL, "\0")
        return self.tokens
