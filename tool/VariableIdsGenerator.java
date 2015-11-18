package tool;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class VariableIdsGenerator {

    private static final String VAR_FORMAT = "%sa%d";

    private Map<String, Integer> freshIds;

    public VariableIdsGenerator() {
        freshIds = new HashMap<>();
    }

    // HELPER methods start
    Integer generateFresh(String name) {
        Integer prevUse = freshIds.get(name);
        Integer newId = prevUse == null ? 0 : prevUse + 1;
        freshIds.put(name, newId);

        return newId;
    }

    List<String> listAllUsedVariables() {
        List<String> result = new LinkedList<>();
        for (Map.Entry<String, Integer> entry : freshIds.entrySet()) {
            for (int idx = 0; idx <= entry.getValue(); idx++) {
                result.add(String.format(VAR_FORMAT, entry.getKey(), idx));
            }
        }

        return result;
    }
}
