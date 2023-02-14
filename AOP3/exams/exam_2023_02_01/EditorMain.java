public class EditorMain {
    public static void main(String[] args) {
        NaiveTextEditor nte = new NaiveTextEditor();

        // Add 11 chars
        for (char i = 'a'; i < 'l'; i++)
            nte.addChar(i);

        System.out.println(nte);

        nte.undo();
        nte.undo();
        System.out.println(nte);

        // Delete 3 chars
        for (int i = 0; i <= 2; i++)
            nte.delChar();

        System.out.println(nte);

        nte.undo();
        System.out.println(nte);

        nte.redo(1);
        System.out.println(nte);

        // Undo 3 times
        for (int i = 0; i < 3; i++)
            nte.undo();

        System.out.println(nte);

        nte.redo(2);
        System.out.println(nte);

        // System.out.println(UndoRedoAspect.aspectOf(nte));
    }
}

// Compile and run with: ajc -1.9 *.aj *.java && aj EditorMain
// Remove *.class: rm -f *.class

// Output:
// [a, b, c, d, e, f, g, h, i, j, k]
// [a, b, c, d, e, f, g, h, i]
// [a, b, c, d, e, f]
// [a, b, c, d, e, f, g]
// [a, b, c, d, e, f]
// [a, b, c, d, e, f, g, h, i]
// [a, b, c, d, e, f, g, h]

// Annotated:
// [a, b, c, d, e, f, g, h, i, j, k] - Line 9  | addChar() 11 times
// [a, b, c, d, e, f, g, h, i]       - Line 13 | undo()    2 times
// [a, b, c, d, e, f]                - Line 19 | delChar() 3 times
// [a, b, c, d, e, f, g]             - Line 22 | undo()    1 time
// [a, b, c, d, e, f]                - Line 25 | redo(1)   1 time
// [a, b, c, d, e, f, g, h, i]       - Line 31 | undo()    3 times
// [a, b, c, d, e, f, g, h]          - Line 34 | redo(2)   1 time
