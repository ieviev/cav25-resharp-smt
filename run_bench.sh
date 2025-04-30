#!/usr/bin/env bash

# Extracts the tool version from the line containing substring ";version-result".
get_tool_version() {
	local line_with_version="$1"
	line_with_version=${line_with_version%-result*}
	line_with_version=${line_with_version##*;}
	echo ${line_with_version%;}
}

process_tasks() {
	local dir=$3
	local file_name=dir/$1
	local tool_name=$2
	cat $dir/*.tasks | python3 pyco_proc --csv > $dir/to120.csv
}

TIMEOUT=6
j_value="1"
m_value="8"
# dont include "singlefile" by default, as it takes a very long time
ALL_BENCH=("sygus_qgen" "denghang" "automatark" "boolean_and_loops" "date" "det_blowup" "password" "regexlib_membership" "regexlib_intersection" "regexlib_subset" "state_space")
ALL_TOOLS=("resharp-solver" "z3-noodler" "cvc5" "z3" "z3str3" "z3str4" "ostrich" "ostrichrecl" "z3alpha")

show_help() {
	echo "Usage:"
	echo "run_bench.sh [options] [BENCHMARK1 BENCHMARK2 BENCHMARK3 ...]"
	echo ""
	echo "Example: ./run_bench.sh -t resharp-solver date det_blowup"
        echo ""
	echo "Runs given tool(s) on given benchmark(s). If no benchmark is given,"
	echo "all benchmarks are run. The possible benchmarks are:"
	echo "${ALL_BENCH[@]}"
	echo "Options:"
	echo "  -h      Show this help message"
	echo "  -t TOOL Which tool to run. Can be given multiple times, if not"
	echo "          given, all tools are run. The possible tools are:"
	echo "          ${ALL_TOOLS[@]}"
	echo "  -j N    How many processes to run in parallel (default=$j_value)"
	echo "  -m N    Memory limit of each process in GB (default=$m_value)"
	echo "  -s      If set, runs only 2 instances for each benchmark"
}

declare -A tool_mapping=( 
    ["resharp-solver"]="resharp-solver" 
    ["z3-noodler"]="z3-noodler-e4535f1010356a7aa074121e399d87d23fddc0bc" 
    ["cvc5"]="cvc5-1.2.0" 
    ["z3"]="z3-4.13.4" 
    ["z3str3"]="z3str3-4.13.4" 
    ["z3str4"]="z3str4" 
    ["z3alpha"]="z3alpha" 
    ["ostrich"]="ostrich" 
    ["ostrichrecl"]="ostrichrecl" 
    )

declare -A tool_loops=( 
    ["resharp-solver"]="1" 
    ["z3-noodler"]="1" 
    ["cvc5"]="1" 
    ["z3"]="1" 
    ["z3str3"]="1" 
    ["z3str4"]="1" 
    ["z3alpha"]="1" 
    ["ostrich"]="1" 
    ["ostrichrecl"]="1" 
    )

tools=()

run_small=false

while getopts "hst:j:m:" option; do
    case $option in
        h)
            show_help 
            exit 0
            ;;
        s)
			run_small=true
			;;
        t)
			tools+=("$OPTARG")
            ;;
        j)
            j_value=$OPTARG
            ;;
        j)
            m_value=$OPTARG
            ;;
        *)
            echo "Invalid option: -$OPTARG"
            show_help
            exit 1
            ;;
    esac
done

# If no tool is given, run all
if [ ${#tools[@]} -eq 0 ]; then
  tools=("${ALL_TOOLS[@]}")
fi

# Shift the option index so that $1 refers to the first positional argument
shift $((OPTIND - 1))

benchmarks=()

# If no benchmark is given, run all
if [ -z "$1" ]; then
  benchmarks=("${ALL_BENCH[@]}")
else
	for BENCH_NAME in "$@"
	do
		benchmarks+=("$BENCH_NAME")
	done
fi

results_dir="results"
if [ "$run_small" = true ] ; then
	results_dir="results-short"
fi

for benchmark in "${benchmarks[@]}"; do
	tasks_file_final_location="$results_dir/$benchmark"
	mkdir --parents "$tasks_file_final_location"
	for tool in "${tools[@]}"; do
		cd inputs
		echo "Running benchmark $benchmark for $tool"
		TASKS_FILE="$benchmark-to120-$tool.tasks"
		if [ "$run_small" = true ] ; then
			head -n 2 "$benchmark.input" | ./pycobench -c smt.yaml -j $j_value -t $TIMEOUT --memout $m_value -m "${tool_mapping[$tool]}" --loops "${tool_loops[$tool]}" -o "$TASKS_FILE"
		else
			cat "$benchmark.input" | ./pycobench -c smt.yaml -j $j_value -t $TIMEOUT --memout $m_value -m "${tool_mapping[$tool]}"  --loops "${tool_loops[$tool]}"  -o "$TASKS_FILE"
		fi
		cd ..
		mv "inputs/$TASKS_FILE" "$tasks_file_final_location/$TASKS_FILE"
		# process_tasks "$TASKS_FILE" $tool $tasks_file_final_location
	done
	cat $tasks_file_final_location/*.tasks | python3 pyco_proc --csv > $tasks_file_final_location/to120.csv
done
