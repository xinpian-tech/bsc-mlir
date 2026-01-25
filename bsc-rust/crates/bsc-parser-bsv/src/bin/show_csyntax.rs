//! BSV show-csyntax binary for differential testing.
//!
//! This binary parses a BSV file and outputs CSyntax in the same format
//! as `bsc -show-csyntax` for comparison.

use bsc_parser_bsv::parse_package_with_file;
use std::env;
use std::fs;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <file.bsv>", args[0]);
        return ExitCode::FAILURE;
    }

    let filename = &args[1];

    let source = match fs::read_to_string(filename) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading {}: {}", filename, e);
            return ExitCode::FAILURE;
        }
    };

    match parse_package_with_file(&source, filename) {
        Ok(pkg) => {
            println!("{}", pkg);
            ExitCode::SUCCESS
        }
        Err(errors) => {
            for err in errors {
                eprintln!("Error: {}", err.message);
            }
            ExitCode::FAILURE
        }
    }
}
