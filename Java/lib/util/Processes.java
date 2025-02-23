package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;

public final class Processes {

    public static void run(String command) throws Exception {
        Process process = Runtime.getRuntime()
                .exec(command);

        try (BufferedReader output = new BufferedReader(new InputStreamReader(process.getInputStream())); //
                 BufferedReader error = new BufferedReader(new InputStreamReader(process.getErrorStream()));) {
            output.lines().forEach(l -> System.out.println(l));
            error.lines().forEach(l -> System.out.println(l));
        }
    }

    public static void run(String command, String dir) throws Exception {
        Process process = Runtime.getRuntime()
                .exec(command, null, new File(dir));

        try (BufferedReader output = new BufferedReader(new InputStreamReader(process.getInputStream())); //
                 BufferedReader error = new BufferedReader(new InputStreamReader(process.getErrorStream()));) {
            output.lines().forEach(l -> System.out.println(l));
            error.lines().forEach(l -> System.out.println(l));
        }
    }
}
