# Artifact for "Regex Decision Procedures in Extended RE#"
In this artifact, we provide the source code and required materials to reproduce our results as described in our paper.
This appendix describes how to replicate the experiments as
described in **§5** in our paper.

The artifact is hosted at https://zenodo.org/records/15210806

# Getting Started
First, you need to ensure that `Docker` is installed in your machine.

Instructions about how to install `Docker` are at https://docs.docker.com/engine/install/.

## Mac users
Please use Docker Desktop version  v4.34.3 or later. Please tick the "Use Rosetta for x86_64/amd64 emulation on Apple Silicon" tick box in Settings -> General.



## Prerequisites 
This artifact uses Docker to run the benchmark. No other dependencies are required.

Make sure you have at least 20GB of disk space, the uncompressed docker image is about 10 GBs in size, and contains the git repositories used to build all the other tools in the comparison. 

A compressed directory with a pre-built docker image is available at zenodo as `cav25.tar.xz`. To extract the directory run the following command:

```shell
tar -xJvf cav25.tar.xz
```

## Preparation

The directory cav25 contains a docker image along with scripts to run the experiments.


### Loading the docker image

To prepare the docker image, run the following command in the cav25 directory:
```shell
docker image load -i docker-container.tar
```
To check if the image was successfully imported, run the following command.
```shell
docker image ls
```
If the image was successfully imported, you can see an image named `cav25` after running this command.


### Running the benchmarks

To run the benchmarks we have provided 2 scripts with identical command line options
```shell
run_bench.sh
```

and

```shell
run_bench_singlerun.sh
```

When invoked with no command line option, they default to running all benchmarks with all tools a single process at a time.

For some of the tools running some of the benchmarks with a single invocation of the command yields 0.0 s as the result is below the resolution of /usr/bin/time (0.01 s). The `run_bench_singlerun.sh`
runs each tool on each benchmark just once, but does not produce accurate timing data. The command `run_bench.sh` repeats the commands 10 to 1000 times depending on the tool to average out run times
and provide better runtime resolution down to tenths of milliseconds.

Help is displayed with

```shell
run_bench_singlerun.sh --help
```

The tool `resharp-solver` can be run with benchmark `date` using the following command line:

```shell
run_bench_singlerun.sh -t resharp-solver date
```

If the processor has many cores, one can use the `-j` option (note, as e.g. Ostrich uses multiple cores, the argument to `-j` should be at least 4 times lower than the core count. E.g. if there are at least 32 cores available, run

```shell
run_bench_singlerun.sh -t resharp-solver -j 8 date
```

The default memory limit is 8 GB.


The possible benchmarks are:
- `sygus_qgen` (~400 benchmarks)
- `denghang` (~1000 benchmarks)
- `automatark` (~16 000 benchmarks)
- `boolean_and_loops` (21 benchmarks)
- `date` (20 benchmarks)
- `det_blowup` (14 benchmarks)
- `password` (34 benchmarks)
- `regexlib_membership` (~1900 benchmarks)
- `regexlib_intersection` (55 benchmarks)
- `regexlib_subset` (100 benchmarks)
- `state_space` (22 benchmarks)
- `singlefile` (all benchmarks concatenated as a single file, excluded by default)

The possible solvers are:
- `resharp-solver`
- `z3-noodler`
- `cvc5`
- `z3`
- `z3str3`
- `z3str4`
- `ostrich`
- `ostrichrecl`
- `z3alpha`

...

To view the exact versions of tools used, see the contents of the `/tools` 
directory inside the container. Each tool points to the location of the source repository used to build it.
```sh
root@0d24566bae74:/tools# ls -l
total 40
lrwxrwxrwx 1 root root  19 Apr 13 16:17 cvc5 -> /cvc5/prod/bin/cvc5
-rwxr-xr-x 1 root root 245 Apr 11 18:42 cvc5-wrap.sh
lrwxrwxrwx 1 root root  16 Apr 13 16:17 ostrich -> /ostrich/ostrich
-rwxr-xr-x 1 root root 282 Apr 11 18:40 ostrich-wrap.sh
lrwxrwxrwx 1 root root  24 Apr 13 16:17 ostrichrecl -> /ostrichrecl/ostrichrecl
-rwxr-xr-x 1 root root 248 Apr 11 18:40 ostrichrecl-wrap.sh
lrwxrwxrwx 1 root root  52 Apr 13 16:17 resharp-solver -> /source/resharp-solver/target/release/resharp-solver
-rwxr-xr-x 1 root root 233 Apr 11 18:41 resharp-solver-wrap.sh
lrwxrwxrwx 1 root root  12 Apr 13 16:17 z3 -> /z3/build/z3
lrwxrwxrwx 1 root root  28 Apr 13 16:17 z3-noodler -> /z3-noodler/build/z3-noodler
-rwxr-xr-x 1 root root 297 Apr 11 18:42 z3-noodler-wrap.sh
-rwxr-xr-x 1 root root 276 Apr 11 18:43 z3-wrap.sh
-rwxr-xr-x 1 root root 228 Apr 11 18:43 z3alpha-wrap.sh
lrwxrwxrwx 1 root root  29 Apr 13 16:17 z3alpha.py -> /z3alpha/smtcomp24/z3alpha.py
-rwxr-xr-x 1 root root 282 Apr 11 18:46 z3str3-wrap.sh
lrwxrwxrwx 1 root root  14 Apr 13 16:17 z3str4 -> /z3str4/z3str4
-rwxr-xr-x 1 root root 384 Apr 11 18:46 z3str4-wrap.sh
```


The artifact uses a modified version of Pycobench to run benchmarks and collect the data.

Waiting for the timeouts in full results can take very long, so we recommend running a subset of the benchmarks first with `run_bench_singlerun.sh`, and then comparing the tools with `run_bench.sh` for more accurate measurements after.

## Other scripts

We also provide some scripts that mount `./results` and `./figs/` inside the container, so the results can be viewed on the host machine. We encourage you to inspect and modify these scripts as needed.
The scripts are described as follows:
- `interactive_shell.sh` enters a shell inside the container
- `run_bench_singlerun.sh` and `run_bench.sh` run benchmarks inside the container. see `Running the benchmarks` for options
- `run_benchmarks_small.sh` runs a subset of the benchmarks without extra repetitions for accuracy
- `run_benchmarks_long.sh` runs all the benchmarks with extra repetitions (warning: this can take more than a day waiting for timeouts)
- `create-figures.sh` generates the plot from the contents of the `./results` directory
- `export_benchmarks.sh` exports the benchmark SMT files to `./formulae/`
- `export_source.sh` exports the source directory for `resharp-solver` to `./src/`


## Reusability

the source code for `resharp-solver` is located in the `source/` directory of the container and on GitHub at https://github.com/ieviev/cav25-resharp-smt



