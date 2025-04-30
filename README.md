# Artifact for "Regex Decision Procedures in Extended RE#"
In this artifact, we provide the source code and required materials to reproduce our results as described in our paper.
This appendix describes how to replicate the experiments as
described in **§5** in our paper.

The artifact is hosted at https://doi.org/10.5281/zenodo.15210805

Supported claims:
- a) Cactus plot in Figure 1
- b) Timeout results in Table 1

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

To run the benchmarks we have provided 2 scripts with identical command line options: `run_bench.sh` and `run_bench_with_repetitions.sh`

When invoked with no command line option, they default to running all benchmarks with all tools a single process at a time.

`run_bench.sh` runs each tool on each benchmark just once, but does not produce accurate timing data. The command `run_bench_with_repetitions.sh` repeats the commands 10 to 1000 times depending on the tool to average out run times and provide better runtime resolution down to tenths of milliseconds.

Help is displayed with

```shell
run_bench.sh --help
```

The tool `resharp-solver` can be run with benchmark `date` using the following command line:

```shell
run_bench.sh -t resharp-solver date
```

If the processor has many cores, one can use the `-j` option (note, as e.g. Ostrich uses multiple cores, the argument to `-j` should be at least 4 times lower than the core count. E.g. if there are at least 32 cores available, run

```shell
run_bench.sh -t resharp-solver -j 8 date
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

## Other scripts

We also provide some scripts that mount `./results` and `./figs/` inside the container, so the results can be viewed on the host machine. We encourage you to inspect and modify these scripts as needed.
The scripts are described as follows:
- `interactive_shell.sh` enters a shell inside the container
- `run_bench_singlerun.sh` and `run_bench.sh` run benchmarks inside the container. see `Running the benchmarks` for options
- `create-figures.sh` generates the cactus plot and timeouts table from the contents of the `./results` directory at `./figs/plot.png` and `./figs/timeouts.txt` respectively.
- `export_benchmarks.sh` exports the benchmark SMT files to `./formulae/`
- `export_source.sh` exports the source directory for `resharp-solver` to `./src/`


## Scripts to run for the evaluation:

First, we recommend running `run_benchmarks_small.sh` for a small evaluation, this runs a small subset of difficult problems for all solvers and should take around 10 minutes to complete.

Running `create-figures.sh` after this produces a plot in `./figs/plot.png`, where a large amount results are cut at 0.01s. This plot shows that `resharp-solver` has a large number of benchmarks that finished below this resolution of 0.01s.

Next we recommend running `./run_bench.sh -t resharp-solver singlefile`, which runs all ~20 000 benchmarks separated into 4 large files. This should finish in around 3 seconds for `resharp-solver`. This shows that the benchmarks individually take very little time, where the python wrapper often takes more time than the test itself. Other solvers will not be able to finish this set of benchmarks before the timeout threshold.

Next, clear the contents of the `./results` directory, (in case the directory permissions are wrong on linux, you can run `sudo chown -R $USER results/` to reclaim the directory from docker).

Then we recommend running a small set of benchmarks with accurate results below the resolution of 0.01 in `./run_benchmarks_with_repetitions_small.sh`, after which running `create-figures.sh` should show `resharp-solver` consistently outperforming the rest of the solvers. This script should take a couple hours on a single core, but this time can be reduced by setting the `NUM_JOBS` variable inside the `./run_benchmarks_with_repetitions_small.sh` script to run several benchmarks in parallel.

For the full set of benchmarks we recommend starting with solvers that do not have many timeouts, e.g., `./run_bench.sh -t resharp-solver` , `./run_bench.sh -t z3-noodler`. 
Both of these solvers should finish under 15 minutes. For solvers with more timeouts this
will take vastly longer, as each individual timeout will take 6s (with ~20 000 benchmarks this means up to 32 hours of timeouts). Running `create-figures.sh` after these benchmarks produces the results of Table 1 for timeouts in `./figs/timeouts.txt`.

The rest of the scripts are optional as they take much longer to evaluate.

To produce more accurate results below the resolution of 0.01s for the full set of benchmarks, you can run e.g., `./run_bench_with_repetitions.sh -t resharp-solver`. This takes around 2s per benchmark, which takes over 10 hours for `resharp-solver` on a single core.

Running all benchmarks with repetitions for all solvers `run_benchmarks_long.sh` may take **up to a week** to complete, running `create-figures.sh` after this command will produce results shown in Figure 1.

## Generating the plot and table

After the benchmarks have finished, the results data is stored in the `./results` directory.
The script `create-figures.sh` can be used to generate both the cactus plot as `./figs/plot.png` and the timeouts table as `./figs/timeouts.txt` in LaTeX format from the contents of the `./results` directory.


## Reusability

the source code for `resharp-solver` is located in the `source/` directory of the container and on GitHub at https://github.com/ieviev/cav25-resharp-smt

- the Dockerfile used to build the container is located at the root of the GitHub repository
- the tool can be used as a regex sat solver by passing a `.smt2` file as an argument: (see `source/resharp-solver/src/main.rs`)
- the solver can also be used in a rust library directly e.g., see the solver implementation (`source/resharp-solver/src/resharp_smt.rs`) for examples



