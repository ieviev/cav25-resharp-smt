use std::thread;

pub mod resharp_smt;
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let input = if cfg!(feature = "testing") {
        // used for debugging
        // "/bench/examples/example2.smt2"
        "/bench/examples/example3.smt2"
    } else {
        &args[1]
    };

    let string = std::fs::read(input).unwrap();

    // start timer
    let start = std::time::Instant::now();

    // run with increased stack size (not really required here but nice to have)
    let result = thread::Builder::new()
        .stack_size(32 * 1024 * 1024 * 64)
        .spawn(move || {
            return resharp_smt::run_smt(&string);
        })
        .unwrap()
        .join()
        .unwrap();

    // let result = resharp_smt::run_smt(&string);
    let output = match result {
        Ok(cmds) => cmds,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };
    for cmd in output {
        println!("{}", cmd);
    }
    if cfg!(feature = "testing") {
        let duration = start.elapsed();
        println!("time: {:?}", duration);
    }
}
