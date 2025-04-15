open System.Collections.Generic
open System.IO
open System.Text.Json
open System.Diagnostics

System.Environment.CurrentDirectory <- __SOURCE_DIRECTORY__

let figs_path = "../figs"
let mkplot_script = __SOURCE_DIRECTORY__ + "/mkplot/mkplot.py"
let figs_data_path = "../figs/data"
let value_if_zero = 0.001
let value_if_failed = 6.

let run_process(name, args: string, work_directory: string) =
    task {
        use p =
            new Process(
                StartInfo =
                    ProcessStartInfo(
                        fileName = name,
                        arguments = args,
                        WorkingDirectory = work_directory,
                        UseShellExecute = true
                    )
            )

        let _ = p.Start()
        do! p.WaitForExitAsync()
        return p.ExitCode
    }

// ensure paths exist
run_process("mkdir", $"-p {figs_data_path}", __SOURCE_DIRECTORY__).Wait()

type SatResult =
    | Sat
    | Unsat
    | Unknown
    | Timeout
    | Other of string

type CactusResult = {
    status: bool
    rtime: double
    [<Serialization.JsonIgnoreAttribute>]
    res: SatResult
}

type Preamble = { prog_alias: string }
type CactusData = { stats: Dictionary<string, CactusResult>; preamble: Preamble }

type BenchResult = {
    path: string
    time: double
    [<Serialization.JsonIgnoreAttribute>]
    result: SatResult
} with

    static member ofLine(line: string) =
        if line.StartsWith("timeout;") then
            {
                path = ""
                result = Timeout
                time = 0.
            }
        else
            let values: string array = line.Split(';')

            let result =
                match values.[4] with
                | "0###result: sat" -> Sat
                | "0###result: unsat" -> Unsat
                | "0###result: unknown" -> Unknown
                | "1###result:TO" -> Timeout
                | _ -> Other(values.[4])


            {
                path = values.[2]
                result =
                    match values.[4] with
                    | "0###result: sat" -> Sat
                    | "0###result: unsat" -> Unsat
                    | "0###result: unknown" -> Unknown
                    | "1###result:TO" -> Timeout
                    | _ -> Other(values.[4])
                time =
                    match result with
                    | Sat
                    | Unsat ->
                        let time = float values.[6]
                        if time = 0. then value_if_zero else time
                    | _ -> value_if_failed
            }


// "../results/sygus_qgen"; "../results/automatark"; ...
let result_folders = Directory.EnumerateDirectories("../results") |> Seq.toArray

let get_tasks (folder: string array) (tool_name: string) =
    folder
    |> Array.map (fun folder ->
        let folder_name = Path.GetFileNameWithoutExtension folder
        let file = Path.Combine(folder, $"{folder_name}-to120-{tool_name}.tasks")

        if File.Exists file then
            let lines = File.ReadAllLines file

            let finished =
                lines
                |> Seq.where (fun line ->
                    line.StartsWith("finished;") || line.StartsWith("timeout;")
                )
                |> Seq.toArray

            Some(folder, finished)
        else
            None
    )
    |> Array.choose id

let get_timeouts (folders: string array) (tool_name: string) =
    folders
    |> Array.map (fun folder ->
        let file =
            Path.Combine(
                folder,
                $"{Path.GetFileNameWithoutExtension folder}-to120-{tool_name}.tasks"
            )

        if File.Exists file then
            let lines = File.ReadAllLines file

            let timeout_result =
                lines
                |> Seq.where (fun line -> line.StartsWith("timeout;"))
                |> Seq.toArray
                |> Seq.length

            let unknown_result =
                lines
                |> Seq.where (fun line -> line.StartsWith("finished;"))
                |> Seq.map BenchResult.ofLine
                |> Seq.where (fun v -> v.result = SatResult.Unknown)
                |> Seq.toArray
                |> Seq.length

            Some(folder, timeout_result + unknown_result)
        else
            None
    )
    |> Array.choose id
    |> dict

let get_results folder tool_name =
    let data =
        get_tasks folder tool_name
        |> Array.collect (fun (folder, tasks) ->
            tasks
            |> Array.map (fun v ->
                let b = BenchResult.ofLine v
                b.path, b
            )
        )
        |> Seq.map (fun (key, bench) ->
            key,
            match bench.result with
            | SatResult.Timeout -> {
                status = true
                rtime = value_if_failed
                res = bench.result
              }
            | (SatResult.Unknown)
            | SatResult.Other _ -> {
                status = false
                rtime = value_if_failed
                res = bench.result
              }
            | _ ->
                {
                    status = true
                    rtime = if bench.time = 0. then value_if_zero else bench.time
                    res = bench.result
                }
        )
        |> (dict >> Dictionary)

    { stats = data; preamble = { prog_alias = tool_name } }


let resharpsolver = get_results result_folders "resharp-solver"
let cvc = get_results result_folders "cvc5"
let z3noodler = get_results result_folders "z3-noodler"
let ostrich = get_results result_folders "ostrich"
let ostrichrecl = get_results result_folders "ostrichrecl"
let z3 = get_results result_folders "z3"
let z3str4 = get_results result_folders "z3str4"
let z3str3 = get_results result_folders "z3str3"
let z3alpha = get_results result_folders "z3alpha"

let export_mkplot() =
    stdout.WriteLine $"exporting solver results to {figs_data_path}/"

    let save (data: CactusData) name =
        if data.stats.Count > 0 then
            stdout.WriteLine $"writing: {name}"
            let json = JsonSerializer.SerializeToUtf8Bytes(data)
            File.WriteAllBytes($"{figs_data_path}/{name}.json", json)


    save ostrichrecl "solver1"
    save ostrich "solver2"
    save z3alpha "solver3"
    save z3str3 "solver4"
    save z3str4 "solver5"
    save z3 "solver6"
    save z3noodler "solver7"
    save cvc "solver8"
    save resharpsolver "solver9"


let generate_plot_image =

    export_mkplot ()

    //stdout.WriteLine $"generating plot to {figs_path}/plot.pdf"
    stdout.WriteLine $"generating plot to {figs_path}/plot.png"

    let solver_json_files =
        Directory.EnumerateFiles(figs_data_path, "*.json") |> String.concat " "

    let plot_args =
        String.concat " " [
            "-l"
            "--legend prog_alias"
            "--ymax 10"
            "--ymin 0.0001"
            "--font-sz 18"
            "--backend=png" // "--backend=pdf"
            "--ylog"
            solver_json_files
        ]

    run_process("/usr/bin/env", $"python \"{mkplot_script}\" {plot_args}", figs_path).Wait()

(*
    stdout.WriteLine $"converting {figs_path}/plot.pdf to {figs_path}/plot.png"

    run_process(
        "/usr/bin/env",
        $"gs -sDEVICE=png16m -dTextAlphaBits=4 -r300 -o plot.png plot.pdf",
        figs_path
    )
        .Wait()
    *)

let get_failed (name: string) (data: CactusData) =
    data.stats
    |> Seq.where (fun v -> v.Key.StartsWith(name) && (v.Value.status <> true))
    |> Seq.toArray

let benchPrefix = {|
    automatark = "../formulae/QF_S/20230329-automatark-lu/"
    sygus_qgen = "../formulae/QF_S/2020-sygus-qgen/"
    denghang = "../formulae/QF_SLIA/20230329-denghang/"

    boolean_and_loops = "../formulae/regex-smt-benchmarks/boolean_and_loops/"
    date = "../formulae/regex-smt-benchmarks/date/"
    det_blowup = "../formulae/regex-smt-benchmarks/det_blowup/"
    password = "../formulae/regex-smt-benchmarks/password/"
    regexlib_intersection = "../formulae/regex-smt-benchmarks/regexlib_intersection/"
    regexlib_membership = "../formulae/regex-smt-benchmarks/regexlib_membership/"
    regexlib_subset = "../formulae/regex-smt-benchmarks/regexlib_subset/"
    state_space = "../formulae/regex-smt-benchmarks/state_space/"
|}

let get_all_failed data = [|
    get_failed benchPrefix.automatark data
    get_failed benchPrefix.sygus_qgen data
    get_failed benchPrefix.denghang data
    get_failed benchPrefix.boolean_and_loops data
    get_failed benchPrefix.date data
    get_failed benchPrefix.det_blowup data
    get_failed benchPrefix.password data
    get_failed benchPrefix.regexlib_intersection data
    get_failed benchPrefix.regexlib_membership data
    get_failed benchPrefix.regexlib_subset data
    get_failed benchPrefix.state_space data
|]

let to_resh = get_timeouts result_folders "resharp-solver"
let to_z3noodler = get_timeouts result_folders "z3-noodler"
let to_ostrich = get_timeouts result_folders "ostrich"
let to_ostrichrecl = get_timeouts result_folders "ostrichrecl"
let to_z3 = get_timeouts result_folders "z3"
let to_cvc = get_timeouts result_folders "cvc5"
let to_z3str4 = get_timeouts result_folders "z3str4"
let to_z3str3 = get_timeouts result_folders "z3str3"
let to_z3alpha = get_timeouts result_folders "z3alpha"

let timeouts_line (toolname: string) (data: IDictionary<string, int>) =
    if data.Count = 0 then
        ""
    else

    let get_or_0(s) =
        match data.TryGetValue(s) with
        | true, v -> v
        | _ -> 0

    let indiv = [
        get_or_0 "../results/sygus_qgen"
        get_or_0 "../results/denghang"
        get_or_0 "../results/automatark"
        get_or_0 "../results/boolean_and_loops"
        get_or_0 "../results/date"
        get_or_0 "../results/det_blowup"
        get_or_0 "../results/password"
        get_or_0 "../results/regexlib_membership"
        get_or_0 "../results/regexlib_intersection"
        get_or_0 "../results/regexlib_subset"
        get_or_0 "../results/state_space"
    ]

    let indivsum = Seq.sum indiv

    indiv
    |> Seq.map (fun v ->
        match v with
        | 0 -> @"\mn{0}"
        | _ -> $@"\mx{{{v}}}"
    )
    |> String.concat " & "
    |> (fun v -> toolname + " & " + v + $" & {indivsum}" + @" \\\hline")


let timeouts_table =
    [
        timeouts_line @"\REs-solver" to_resh
        timeouts_line @"Z3-Noodler" to_z3noodler
        timeouts_line @"OSTRICH" to_ostrich
        timeouts_line @"OSTRICH-RECL" to_ostrichrecl
        timeouts_line @"cvc5" to_cvc
        timeouts_line @"Z3" to_z3
        timeouts_line @"Z3alpha" to_z3alpha
        timeouts_line @"Z3str4" to_z3str4
        timeouts_line @"Z3str3" to_z3str3
    ]
    |> Seq.where (fun v -> v <> "")
    |> String.concat "\n"
    |> (fun v -> File.WriteAllText(figs_path + "/timeouts.txt", v))


// sanity check: all results should be the same
// resharp-solver as baseline

let compare_results(data: CactusData) =
    for s in data.stats do
        match resharpsolver.stats.TryGetValue(s.Key) with
        | false, _ -> ()
        | true, other ->
            // unknown results
            if s.Value.res = SatResult.Unknown then
                ()
            else if other.res <> s.Value.res then
                failwithf "%s: %A %A" s.Key other.res s.Value.res

compare_results z3
compare_results cvc
compare_results z3noodler

stdout.WriteLine $"results processed, see {figs_path} for figures and tables"
