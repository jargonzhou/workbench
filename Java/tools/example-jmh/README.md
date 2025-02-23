# JMH
- https://github.com/openjdk/jmh
- [JMH Visualizer](https://github.com/jzillmann/jmh-visualizer)

## Running

```shell
mvn archetype:generate \
  -DinteractiveMode=false \
  -DarchetypeGroupId=org.openjdk.jmh \
  -DarchetypeArtifactId=jmh-java-benchmark-archetype \
  -DgroupId=com.spike \
  -DartifactId=example-jmh \
  -Dversion=1.0
```

```shell
$ mvn clean verify
$ java -jar target/benchmarks.jar -h
Usage: java -jar ... [regexp*] [options]
 [opt] means optional argument.
 <opt> means required argument.
 "+" means comma-separated list of values.
 "time" arguments accept time suffixes, like "100ms".

Command line options usually take precedence over annotations.

  [arguments]                 Benchmarks to run (regexp+). (default: .*)

  -i <int>                    Number of measurement iterations to do. Measurement
                              iterations are counted towards the benchmark score.
                              (default: 1 for SingleShotTime, and 5 for all other
                              modes)

  -bs <int>                   Batch size: number of benchmark method calls per
                              operation. Some benchmark modes may ignore this
                              setting, please check this separately. (default:
                              1)

  -r <time>                   Minimum time to spend at each measurement iteration.
                              Benchmarks may generally run longer than iteration
                              duration. (default: 10 s)

  -wi <int>                   Number of warmup iterations to do. Warmup iterations
                              are not counted towards the benchmark score. (default:
                              0 for SingleShotTime, and 5 for all other modes)

  -wbs <int>                  Warmup batch size: number of benchmark method calls
                              per operation. Some benchmark modes may ignore this
                              setting. (default: 1)

  -w <time>                   Minimum time to spend at each warmup iteration. Benchmarks
                              may generally run longer than iteration duration.
                              (default: 10 s)

  -to <time>                  Timeout for benchmark iteration. After reaching
                              this timeout, JMH will try to interrupt the running
                              tasks. Non-cooperating benchmarks may ignore this
                              timeout. (default: 10 min)

  -t <int>                    Number of worker threads to run with. 'max' means
                              the maximum number of hardware threads available
                              on the machine, figured out by JMH itself. (default:
                              1)

  -bm <mode>                  Benchmark mode. Available modes are: [Throughput/thrpt,
                              AverageTime/avgt, SampleTime/sample, SingleShotTime/ss,
                              All/all]. (default: Throughput)

  -si <bool>                  Should JMH synchronize iterations? This would significantly
                              lower the noise in multithreaded tests, by making
                              sure the measured part happens only when all workers
                              are running. (default: true)

  -gc <bool>                  Should JMH force GC between iterations? Forcing
                              the GC may help to lower the noise in GC-heavy benchmarks,
                              at the expense of jeopardizing GC ergonomics decisions.
                              Use with care. (default: false)

  -foe <bool>                 Should JMH fail immediately if any benchmark had
                              experienced an unrecoverable error? This helps
                              to make quick sanity tests for benchmark suites,
                              as well as make the automated runs with checking error
                              codes. (default: false)

  -v <mode>                   Verbosity mode. Available modes are: [SILENT, NORMAL,
                              EXTRA]. (default: NORMAL)

  -f <int>                    How many times to fork a single benchmark. Use 0 to
                              disable forking altogether. Warning: disabling
                              forking may have detrimental impact on benchmark
                              and infrastructure reliability, you might want
                              to use different warmup mode instead. (default:
                              5)

  -wf <int>                   How many warmup forks to make for a single benchmark.
                              All iterations within the warmup fork are not counted
                              towards the benchmark score. Use 0 to disable warmup
                              forks. (default: 0)

  -o <filename>               Redirect human-readable output to a given file.

  -rff <filename>             Write machine-readable results to a given file.
                              The file format is controlled by -rf option. Please
                              see the list of result formats for available formats.
                              (default: jmh-result.<result-format>)

  -prof <profiler>            Use profilers to collect additional benchmark data.
                              Some profilers are not available on all JVMs and/or
                              all OSes. Please see the list of available profilers
                              with -lprof.

  -tg <int+>                  Override thread group distribution for asymmetric
                              benchmarks. This option expects a comma-separated
                              list of thread counts within the group. See @Group/@GroupThreads
                              Javadoc for more information.

  -jvm <string>               Use given JVM for runs. This option only affects forked
                              runs.

  -jvmArgs <string>           Use given JVM arguments. Most options are inherited
                              from the host VM options, but in some cases you want
                              to pass the options only to a forked VM. Either single
                              space-separated option line, or multiple options
                              are accepted. This option only affects forked runs.

  -jvmArgsAppend <string>     Same as jvmArgs, but append these options after the
                              already given JVM args.

  -jvmArgsPrepend <string>    Same as jvmArgs, but prepend these options before
                              the already given JVM arg.

  -tu <TU>                    Override time unit in benchmark results. Available
                              time units are: [m, s, ms, us, ns]. (default: SECONDS)

  -opi <int>                  Override operations per invocation, see @OperationsPerInvocation
                              Javadoc for details. (default: 1)

  -rf <type>                  Format type for machine-readable results. These
                              results are written to a separate file (see -rff).
                              See the list of available result formats with -lrf.
                              (default: CSV)

  -wm <mode>                  Warmup mode for warming up selected benchmarks.
                              Warmup modes are: INDI = Warmup each benchmark individually,
                              then measure it. BULK = Warmup all benchmarks first,
                              then do all the measurements. BULK_INDI = Warmup
                              all benchmarks first, then re-warmup each benchmark
                              individually, then measure it. (default: INDI)

  -e <regexp+>                Benchmarks to exclude from the run.

  -p <param={v,}*>            Benchmark parameters. This option is expected to
                              be used once per parameter. Parameter name and parameter
                              values should be separated with equals sign. Parameter
                              values should be separated with commas.

  -wmb <regexp+>              Warmup benchmarks to include in the run in addition
                              to already selected by the primary filters. Harness
                              will not measure these benchmarks, but only use them
                              for the warmup.

  -l                          List the benchmarks that match a filter, and exit.

  -lp                         List the benchmarks that match a filter, along with
                              parameters, and exit.

  -lrf                        List machine-readable result formats, and exit.

  -lprof                      List profilers, and exit.

  -h                          Display help, and exit.
```


```shell
~/.sdkman/candidates/java/8.0.402-tem/bin/java -jar target/benchmarks.jar -wi 3 -i 3 -f 1
# JMH version: 1.37
# VM version: JDK 1.8.0_402, OpenJDK 64-Bit Server VM, 25.402-b06
# VM invoker: C:\Users\zhouj\.sdkman\candidates\java\8.0.402-tem\jre\bin\java.exe
# VM options: <none>
# Blackhole mode: full + dont-inline hint (auto-detected, use -Djmh.blackhole.autoDetect=false to disable)
# Warmup: 3 iterations, 10 s each
# Measurement: 3 iterations, 10 s each
# Timeout: 10 min per iteration
# Threads: 1 thread, will synchronize iterations
# Benchmark mode: Throughput, ops/time
# Benchmark: com.spike.MyBenchmark.testIntern

# Run progress: 0.00% complete, ETA 00:01:00
# Fork: 1 of 1
# Warmup Iteration   1: 1130.560 ops/s
# Warmup Iteration   2: 1110.437 ops/s
# Warmup Iteration   3: 1143.586 ops/s
Iteration   1: 1093.811 ops/s
Iteration   2: 1106.686 ops/s
Iteration   3: 1131.665 ops/s


Result "com.spike.MyBenchmark.testIntern":
  1110.721 ±(99.9%) 351.131 ops/s [Average]
  (min, avg, max) = (1093.811, 1110.721, 1131.665), stdev = 19.247
  CI (99.9%): [759.589, 1461.852] (assumes normal distribution)


# Run complete. Total time: 00:01:00

REMEMBER: The numbers below are just data. To gain reusable insights, you need to follow up on
why the numbers are the way they are. Use profilers (see -prof, -lprof), design factorial
experiments, perform baseline and negative tests that provide experimental control, make sure
the benchmarking environment is safe on JVM/OS/HW level, ask for reviews from the domain experts.
Do not assume the numbers tell you what you want them to tell.

Benchmark                Mode  Cnt     Score     Error  Units
MyBenchmark.testIntern  thrpt    3  1110.721 ± 351.131  ops/s
```