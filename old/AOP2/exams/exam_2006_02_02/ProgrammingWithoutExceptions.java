import java.io.BufferedReader;
import java.io.FileReader;

public class ProgrammingWithoutExceptions {
    public static void main(String[] args) {
        BufferedReader in = new BufferedReader(new FileReader("temp.txt"));
        String line = in.readLine();
        int i = 1;

        while (line != null) {
            i++;
            line = in.readLine();
        }

        System.out.println("The file has " + (i - 1) + " rows.");
    }
}

// ajc -1.9 *java *aj && aj ProgrammingWithoutExceptions
