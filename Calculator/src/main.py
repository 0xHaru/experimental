from parser import Parser

from lexer import Lexer

print("Press CTRL + D to quit")

while True:
    try:
        lexer = Lexer(input("> "))
        tokens = lexer.tokenize()
        parser = Parser(tokens)
        ast = parser.parse()
        print(ast.eval())
    except EOFError:
        print()
        exit(0)
    except Exception as e:
        print(e)
