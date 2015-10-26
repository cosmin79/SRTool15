package tool;

enum DEBUG_LEVEL {
    TESTING,
    PROD
}

public class DebugUtil {

    DEBUG_LEVEL level;

    public DebugUtil(DEBUG_LEVEL level) {
        this.level = level;
    }

    public void print(String s) {
        if (level == DEBUG_LEVEL.TESTING) {
            System.out.println(s);
        }
    }
}
