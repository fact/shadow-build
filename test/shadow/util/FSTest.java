package shadow.util;


import clojure.lang.RT;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

/**
 * Created by zilence on 05.06.15.
 */
@RunWith(JUnit4.class)
public class FSTest {


    @Test
    public void testListFiles() throws IOException, InterruptedException {
        Object result = FS.findFilesByExt(Paths.get("cljs-data", "css"), "scss");
        System.out.println(result);

        result = FS.glob(Paths.get("cljs-data", "css"), "*.scss");
        System.out.println(result);

        result = FS.glob(Paths.get("cljs-data", "css"), "**/*.scss");
        System.out.println(result);

        File toBeCreated = new File("cljs-data/css/created.scss");
        if (toBeCreated.exists()) {
            toBeCreated.delete();
        }
        toBeCreated.deleteOnExit();

        File toBeDeleted = new File("cljs-data/css/deleted.scss");
        if (!toBeDeleted.exists()) {
            toBeDeleted.createNewFile();
        }
        toBeDeleted.deleteOnExit();

        File dontCare = new File("cljs-data/css/dont-care.txt");
        dontCare.deleteOnExit();

        FileWatcher wd = FileWatcher.create(Paths.get("cljs-data", "css"), (List<String>) RT.list("scss"));

        File file = new File("cljs-data/css/includes/nested/deeper.scss");
        file.setLastModified(System.currentTimeMillis());

        toBeCreated.createNewFile();
        toBeDeleted.delete();
        dontCare.createNewFile();

        System.out.println(wd.waitForChanges());
    }
}
