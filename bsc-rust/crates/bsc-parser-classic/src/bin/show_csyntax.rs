use bsc_parser_classic::parse_package_with_file;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <file.bs>", args[0]);
        std::process::exit(1);
    }

    let filename = &args[1];
    let source = match fs::read_to_string(filename) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    };

    match parse_package_with_file(&source, filename) {
        Ok(pkg) => {
            println!("{}", pkg);
        }
        Err(errs) => {
            for e in errs {
                eprintln!("Error: {}", e);
            }
            std::process::exit(1);
        }
    }
}
