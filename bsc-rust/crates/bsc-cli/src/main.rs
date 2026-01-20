//! CLI frontend for BSC Rust compiler.

use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "bsc-rust")]
#[command(about = "Bluespec Compiler Frontend (Rust implementation)")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse a file and check for syntax errors
    Parse {
        /// Input file
        file: PathBuf,
        /// Use BSV syntax (default: auto-detect from extension)
        #[arg(long)]
        bsv: bool,
        /// Show tokens instead of AST
        #[arg(long)]
        tokens: bool,
    },
    /// Type check a file
    Check {
        /// Input file
        file: PathBuf,
    },
    /// Export ISyntax as JSON (for differential testing)
    Export {
        /// Input file
        file: PathBuf,
        /// Output file (default: stdout)
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Export format
        #[arg(long, default_value = "json")]
        format: String,
    },
    /// Start LSP server
    Lsp,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Increase stack size for deep recursion in parser
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024) // 128MB stack
        .spawn(|| {
            let cli = Cli::parse();

            let result = match cli.command {
                Commands::Parse { file, bsv, tokens } => cmd_parse(file, bsv, tokens),
                Commands::Check { file } => cmd_check(file),
                Commands::Export {
                    file,
                    output,
                    format,
                } => cmd_export(file, output, format),
                Commands::Lsp => cmd_lsp(),
            };

            if let Err(e) = result {
                eprintln!("Error: {e}");
                std::process::exit(1);
            }
        })
        .expect("Failed to spawn thread")
        .join()
        .expect("Thread panicked");

    Ok(())
}

fn cmd_parse(file: PathBuf, bsv: bool, tokens: bool) -> Result<(), Box<dyn std::error::Error>> {
    let source = std::fs::read_to_string(&file)?;

    // Determine syntax mode
    let is_bsv = bsv || file.extension().is_some_and(|ext| ext == "bsv");

    if is_bsv {
        eprintln!("BSV parsing not yet implemented");
        return Ok(());
    }

    // Classic Bluespec parsing
    use bsc_lexer::{Lexer, SyntaxMode};
    use bsc_parser_classic::process_layout;
    use bsc_syntax::{CDefn, IdK};

    // Tokenize
    let lexer = Lexer::new(&source, SyntaxMode::Classic);
    let raw_tokens = lexer.tokenize().map_err(|e| format!("Lexer error: {e}"))?;

    if tokens {
        println!("Raw tokens ({}):", raw_tokens.len());
        for (i, tok) in raw_tokens.iter().enumerate() {
            println!("  {i:4}: {:?} @ {}:{}", tok.kind, tok.position.line, tok.position.column);
        }

        let layout_tokens = process_layout(raw_tokens);
        println!("\nAfter layout processing ({}):", layout_tokens.len());
        for (i, tok) in layout_tokens.iter().enumerate() {
            println!("  {i:4}: {:?}", tok.kind);
        }
        return Ok(());
    }

    // Helper to get name from IdK
    fn idk_name(idk: &IdK) -> &str {
        match idk {
            IdK::Plain(id) => id.name(),
            IdK::WithKind(id, _) => id.name(),
            IdK::WithPartialKind(id, _) => id.name(),
        }
    }

    // Parse
    match bsc_parser_classic::parse_package(&source) {
        Ok(package) => {
            println!("Successfully parsed package: {}", package.name.name());
            println!("  Imports: {}", package.imports.len());
            println!("  Fixities: {}", package.fixities.len());
            println!("  Definitions: {}", package.definitions.len());

            for defn in &package.definitions {
                match defn {
                    CDefn::Type(td) => {
                        println!("    type {}", idk_name(&td.name));
                    }
                    CDefn::Data(dd) => {
                        println!("    data {}", idk_name(&dd.name));
                    }
                    CDefn::Struct(sd) => {
                        println!("    struct/interface {}", idk_name(&sd.name));
                    }
                    CDefn::Class(cd) => {
                        println!("    class {}", idk_name(&cd.name));
                    }
                    CDefn::Instance(_) => {
                        println!("    instance ...");
                    }
                    CDefn::Value(vd) => {
                        println!("    {} = ...", vd.name.name());
                    }
                    CDefn::ValueSign(def) => {
                        println!("    {} :: ...", def.name().name());
                    }
                    CDefn::Foreign(fd) => {
                        println!("    foreign {}", fd.name.name());
                    }
                    CDefn::Primitive(pd) => {
                        println!("    primitive {}", pd.name.name());
                    }
                    CDefn::PrimitiveType(ptd) => {
                        println!("    primitive type {}", ptd.name.name());
                    }
                    CDefn::Pragma(_) => {
                        println!("    pragma ...");
                    }
                    CDefn::Signature(sig) => {
                        println!("    {} :: ...", sig.name.name());
                    }
                    _ => {
                        println!("    <other definition>");
                    }
                }
            }
        }
        Err(errors) => {
            eprintln!("Parse errors:");
            for err in errors {
                eprintln!("  {err:?}");
            }
            return Err("Parse failed".into());
        }
    }

    Ok(())
}

fn cmd_check(_file: PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    todo!("Check command not yet implemented")
}

fn cmd_export(
    _file: PathBuf,
    _output: Option<PathBuf>,
    _format: String,
) -> Result<(), Box<dyn std::error::Error>> {
    todo!("Export command not yet implemented")
}

fn cmd_lsp() -> Result<(), Box<dyn std::error::Error>> {
    todo!("LSP command not yet implemented")
}
