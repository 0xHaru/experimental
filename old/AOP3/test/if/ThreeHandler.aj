import java.util.Collections;
import java.util.Arrays;
import java.util.List;

privileged public aspect ThreeHandler extends Handler {
    Object around(String[] strings) : matchCons(strings) && if(strings.length == 3) {
        List<String> list = Arrays.asList(strings);
        Collections.reverse(list);
        return proceed(list.toArray(new String[list.size()]));
    }
}
