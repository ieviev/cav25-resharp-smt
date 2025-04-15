#r "nuget: resharp, 0.1.33"
open System.IO

let r =
    Resharp.Regex(
        String.concat "|" [
            // remove set-info lines
            @"^\(set-info~(_*\)\n_*)\)$"
            // remove exit lines
            @"^\(exit\)$"
            // remove comments
            @"^;.*$"
        ]
    )

let create_single_file file_paths out =
    file_paths
    |> Seq.map (fun x -> File.readAllText x)
    |> Seq.map (fun x -> r.Replace(x, ""))
    |> String.concat "\n(reset)\n"
    |> (fun v -> File.WriteAllText(out,v))

let get_all_entries path =
    Directory.EnumerateFiles(path, "*.smt2", SearchOption.AllDirectories) |> Seq.toArray

let formulae_dir = __SOURCE_DIRECTORY__ + "/../formulae/"

let get_formulae dir_relative_to_formulae =
    let path = Path.GetFullPath(Path.Combine(formulae_dir, dir_relative_to_formulae))
    get_all_entries path

let single_sygus =
    create_single_file (get_formulae "QF_S/2020-sygus-qgen") $"{formulae_dir}/singlefile/sygus.smt2"

let single_automatark =
    create_single_file
        (get_formulae "QF_S/20230329-automatark-lu")
        $"{formulae_dir}/singlefile/automatark.smt2"

let single_regex_smt_benchmarks =
    create_single_file
        (get_formulae "regex-smt-benchmarks")
        $"{formulae_dir}/singlefile/regex_smt_benchmarks.smt2"

let single_denghang =
    create_single_file
        (get_formulae "QF_SLIA/20230329-denghang")
        $"{formulae_dir}/singlefile/denghang.smt2"

