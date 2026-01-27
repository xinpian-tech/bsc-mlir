use bsc_preprocess::{preprocess, PreprocessFlags};
use bsc_syntax::CPackage;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rayon::prelude::*;
use rayon::ThreadPoolBuilder;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex, OnceLock};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use similar::{Algorithm, TextDiff};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxMode {
    Classic,
    Bsv,
}

impl SyntaxMode {
    pub fn extension(&self) -> &'static str {
        match self {
            SyntaxMode::Classic => "bs",
            SyntaxMode::Bsv => "bsv",
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            SyntaxMode::Classic => "Classic",
            SyntaxMode::Bsv => "BSV",
        }
    }
}

#[derive(Debug)]
enum FileResult {
    ExactMatch,
    CsyntaxDiff {
        haskell: String,
        rust: String,
    },
    RustParseFailed {
        error: String,
    },
    HaskellParseFailed,
    ReadFailed {
        error: String,
    },
    Timeout,
}

#[derive(Debug)]
struct TestFailure {
    path: PathBuf,
    result: FileResult,
}

fn tokenize_csyntax(input: &str) -> Vec<&str> {
    let mut tokens = Vec::new();
    let bytes = input.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    while i < len {
        match bytes[i] {
            b'(' | b')' | b'[' | b']' | b'{' | b'}' | b',' => {
                tokens.push(&input[i..i + 1]);
                i += 1;
            }
            b' ' | b'\t' | b'\n' | b'\r' => {
                let start = i;
                while i < len && matches!(bytes[i], b' ' | b'\t' | b'\n' | b'\r') {
                    i += 1;
                }
                tokens.push(&input[start..i]);
            }
            _ => {
                let start = i;
                while i < len && !matches!(bytes[i], b'(' | b')' | b'[' | b']' | b'{' | b'}' | b',' | b' ' | b'\t' | b'\n' | b'\r') {
                    i += 1;
                }
                tokens.push(&input[start..i]);
            }
        }
    }
    tokens
}

fn save_outputs(filename: &str, haskell: &str, rust: &str) {
    let dir = PathBuf::from("/tmp/bsc-test-diff");
    let _ = std::fs::create_dir_all(&dir);
    let stem = Path::new(filename)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(filename);
    let h_path = dir.join(format!("{}.haskell.txt", stem));
    let r_path = dir.join(format!("{}.rust.txt", stem));
    let _ = std::fs::write(&h_path, haskell);
    let _ = std::fs::write(&r_path, rust);
    eprintln!("\nOutputs saved to:");
    eprintln!("  Haskell: {}", h_path.display());
    eprintln!("  Rust:    {}", r_path.display());
}

fn print_diff_detail(filename: &str, haskell: &str, rust: &str) {
    save_outputs(filename, haskell, rust);

    let h_tokens = tokenize_csyntax(haskell);
    let r_tokens = tokenize_csyntax(rust);

    let diff = TextDiff::configure()
        .algorithm(Algorithm::Patience)
        .diff_slices(&h_tokens, &r_tokens);

    let h_offsets: Vec<usize> = {
        let mut offsets = Vec::with_capacity(h_tokens.len());
        let mut pos = 0usize;
        for t in &h_tokens {
            offsets.push(pos);
            pos += t.len();
        }
        offsets
    };
    let r_offsets: Vec<usize> = {
        let mut offsets = Vec::with_capacity(r_tokens.len());
        let mut pos = 0usize;
        for t in &r_tokens {
            offsets.push(pos);
            pos += t.len();
        }
        offsets
    };

    let context_tokens = 30;
    eprintln!("\n=== Token-level diff (Patience algorithm) ===");
    eprintln!("Haskell tokens: {}, Rust tokens: {}", h_tokens.len(), r_tokens.len());

    for (idx, group) in diff.grouped_ops(context_tokens).iter().enumerate() {
        let (h_pos, r_pos) = match group.first() {
            Some(similar::DiffOp::Equal { old_index, new_index, .. }) => {
                (h_offsets.get(*old_index).copied().unwrap_or(0),
                 r_offsets.get(*new_index).copied().unwrap_or(0))
            }
            Some(similar::DiffOp::Delete { old_index, new_index, .. }) => {
                (h_offsets.get(*old_index).copied().unwrap_or(0),
                 r_offsets.get(*new_index).copied().unwrap_or(0))
            }
            Some(similar::DiffOp::Insert { old_index, new_index, .. }) => {
                (h_offsets.get(*old_index).copied().unwrap_or(0),
                 r_offsets.get(*new_index).copied().unwrap_or(0))
            }
            Some(similar::DiffOp::Replace { old_index, new_index, .. }) => {
                (h_offsets.get(*old_index).copied().unwrap_or(0),
                 r_offsets.get(*new_index).copied().unwrap_or(0))
            }
            None => (0, 0),
        };
        eprintln!("\n--- Hunk {} (haskell byte {}, rust byte {}) ---", idx + 1, h_pos, r_pos);
        for op in group {
            match op {
                similar::DiffOp::Equal { old_index, len, .. } => {
                    let snippet: String = h_tokens[*old_index..*old_index + *len].concat();
                    if snippet.len() > 120 {
                        let chars: Vec<char> = snippet.chars().collect();
                        let head: String = chars[..60.min(chars.len())].iter().collect();
                        let tail: String = chars[chars.len().saturating_sub(60)..].iter().collect();
                        eprintln!("  = {}...{}", head, tail);
                    } else {
                        eprintln!("  = {}", snippet);
                    }
                }
                similar::DiffOp::Delete { old_index, old_len, .. } => {
                    let snippet: String = h_tokens[*old_index..*old_index + *old_len].concat();
                    eprintln!("  - {}", snippet);
                }
                similar::DiffOp::Insert { new_index, new_len, .. } => {
                    let snippet: String = r_tokens[*new_index..*new_index + *new_len].concat();
                    eprintln!("  + {}", snippet);
                }
                similar::DiffOp::Replace { old_index, old_len, new_index, new_len } => {
                    let old_snippet: String = h_tokens[*old_index..*old_index + *old_len].concat();
                    let new_snippet: String = r_tokens[*new_index..*new_index + *new_len].concat();
                    eprintln!("  - {}", old_snippet);
                    eprintln!("  + {}", new_snippet);
                }
            }
        }
    }
}

pub fn run_differential_test_fail_fast<F>(
    mode: SyntaxMode,
    source_dir: &Path,
    bsc_path: &str,
    parse_fn: F,
)
where
    F: Fn(&str, &str) -> Result<CPackage, String> + Send + Sync + 'static,
{
    let parse_fn = Arc::new(parse_fn);
    let test_file_filter = std::env::var("BSC_TEST_FILE").ok();

    let mut all_files: Vec<_> = walkdir::WalkDir::new(source_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().map_or(false, |ext| ext == mode.extension()))
        .filter(|e| {
            test_file_filter.as_ref().map_or(true, |filter| {
                e.path().to_string_lossy().contains(filter.as_str())
            })
        })
        .map(|e| e.path().to_path_buf())
        .collect();

    let seed: u64 = std::env::var("BSC_TEST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0)
        });

    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    all_files.shuffle(&mut rng);

    let total = all_files.len();
    let passed = AtomicUsize::new(0);
    let skipped = AtomicUsize::new(0);
    let processed = AtomicUsize::new(0);
    let failed = AtomicBool::new(false);
    let first_failure: Mutex<Option<TestFailure>> = Mutex::new(None);

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    let pool = POOL.get_or_init(|| {
        ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .stack_size(64 * 1024 * 1024)
            .build()
            .expect("failed to build thread pool")
    });

    let _ = writeln!(std::io::stderr(), "\n=== {} Differential Test ===", mode.name());
    let _ = writeln!(std::io::stderr(), "Total: {} (using {} threads, seed={})\n", total, num_threads, seed);
    let _ = writeln!(std::io::stderr(), "To reproduce: BSC_TEST_SEED={}", seed);
    let _ = std::io::stderr().flush();

    pool.install(|| all_files.par_iter().for_each(|path| {
        if failed.load(Ordering::Relaxed) {
            return;
        }

        let current = processed.fetch_add(1, Ordering::Relaxed) + 1;
        let filename = path.file_name().map(|s| s.to_string_lossy()).unwrap_or_default();
        let _ = writeln!(std::io::stderr(), "[{}/{}] {} ... parsing", current, total, filename);
        let _ = std::io::stderr().flush();

        let result = test_single_file_with_timeout(path, bsc_path, Arc::clone(&parse_fn), Duration::from_secs(5), mode);

        match &result {
            FileResult::ExactMatch => {
                passed.fetch_add(1, Ordering::Relaxed);
                let _ = writeln!(std::io::stderr(), "[{}/{}] {} ... OK", current, total, filename);
            }
            FileResult::HaskellParseFailed => {
                skipped.fetch_add(1, Ordering::Relaxed);
                let _ = writeln!(std::io::stderr(), "[{}/{}] {} ... SKIP", current, total, filename);
            }
            FileResult::Timeout => {
                let _ = writeln!(std::io::stderr(), "[{}/{}] {} ... TIMEOUT", current, total, filename);
                if !failed.swap(true, Ordering::Relaxed) {
                    let mut guard = first_failure.lock().expect("mutex poisoned");
                    if guard.is_none() {
                        *guard = Some(TestFailure {
                            path: path.clone(),
                            result,
                        });
                    }
                }
            }
            _ => {
                let _ = writeln!(std::io::stderr(), "[{}/{}] {} ... FAIL", current, total, filename);
                if !failed.swap(true, Ordering::Relaxed) {
                    let mut guard = first_failure.lock().expect("mutex poisoned");
                    if guard.is_none() {
                        *guard = Some(TestFailure {
                            path: path.clone(),
                            result,
                        });
                    }
                }
            }
        }
    }));

    let final_passed = passed.load(Ordering::Relaxed);
    let final_skipped = skipped.load(Ordering::Relaxed);

    if let Some(failure) = first_failure.lock().expect("mutex poisoned").take() {
        let _ = writeln!(std::io::stderr(), "\n=== Test Failed ===");
        let _ = writeln!(std::io::stderr(), "Progress: passed={}, skipped={}, total={}", final_passed, final_skipped, total);
        let _ = writeln!(std::io::stderr(), "File: {}", failure.path.display());
        let _ = std::io::stderr().flush();

        match failure.result {
            FileResult::ReadFailed { error } => {
                panic!("READ_FAIL: {}", error);
            }
            FileResult::RustParseFailed { error } => {
                panic!("RUST_FAIL: {}", error);
            }
            FileResult::CsyntaxDiff { haskell, rust } => {
                let filename = failure.path.file_name()
                    .and_then(|s| s.to_str())
                    .unwrap_or("unknown");
                print_diff_detail(filename, &haskell, &rust);
                panic!("CSyntax mismatch");
            }
            FileResult::Timeout => {
                panic!("TIMEOUT: parsing took longer than 5 seconds");
            }
            _ => unreachable!(),
        }
    }

    eprintln!("\n=== All Tests Passed ===");
    eprintln!("Total: {}, Passed: {}, Skipped: {}", total, final_passed, final_skipped);
}

fn test_single_file_with_timeout<F>(
    path: &Path,
    bsc_path: &str,
    parse_fn: Arc<F>,
    timeout: Duration,
    mode: SyntaxMode,
) -> FileResult
where
    F: Fn(&str, &str) -> Result<CPackage, String> + Send + Sync + 'static,
{
    let (tx, rx) = mpsc::channel();
    let path = path.to_path_buf();
    let bsc_path = bsc_path.to_string();

    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let result = test_single_file_inner(&path, &bsc_path, &*parse_fn, mode);
            let _ = tx.send(result);
        })
        .expect("Failed to spawn test thread");

    match rx.recv_timeout(timeout) {
        Ok(result) => result,
        Err(mpsc::RecvTimeoutError::Timeout) => FileResult::Timeout,
        Err(mpsc::RecvTimeoutError::Disconnected) => FileResult::RustParseFailed {
            error: "Test thread panicked".to_string(),
        },
    }
}

fn test_single_file_inner<F>(path: &Path, bsc_path: &str, parse_fn: &F, mode: SyntaxMode) -> FileResult
where
    F: Fn(&str, &str) -> Result<CPackage, String>,
{
    if !path.exists() {
        return FileResult::ReadFailed {
            error: format!("File not found: {}", path.display()),
        };
    }

    let temp_dir = std::env::temp_dir()
        .join("bsc-test")
        .join(format!("thread-{:?}", std::thread::current().id()));
    let _ = std::fs::create_dir_all(&temp_dir);

    let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    let needs_no_prelude = filename == "Prelude.bs" || filename == "PreludeBSV.bsv";

    let mut cmd = Command::new(bsc_path);
    cmd.arg("-show-csyntax").arg("-bdir").arg(&temp_dir);
    if needs_no_prelude {
        cmd.arg("-no-use-prelude");
    }
    cmd.arg(path);

    let haskell_output = cmd.output();

    for entry in std::fs::read_dir(&temp_dir).into_iter().flatten() {
        if let Ok(e) = entry {
            if e.path().extension().map_or(false, |ext| ext == "bo") {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }

    let haskell_csyntax = match haskell_output {
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            if stdout.starts_with("CPackage ") {
                stdout
            } else {
                return FileResult::HaskellParseFailed;
            }
        }
        Err(_) => {
            return FileResult::HaskellParseFailed;
        }
    };

    let source = match mode {
        SyntaxMode::Classic => {
            match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    return FileResult::RustParseFailed {
                        error: format!("Failed to read file: {}", e),
                    };
                }
            }
        }
        SyntaxMode::Bsv => {
            let flags = PreprocessFlags {
                vpp: true,
                ..Default::default()
            };
            match preprocess(path, &flags) {
                Ok(s) => s,
                Err(e) => {
                    return FileResult::RustParseFailed {
                        error: format!("Preprocessing failed: {}", e),
                    };
                }
            }
        }
    };

    let rust_pkg = match parse_fn(&source, &path.to_string_lossy()) {
        Ok(pkg) => pkg,
        Err(e) => {
            return FileResult::RustParseFailed { error: e };
        }
    };

    let rust_csyntax = format!("{}", rust_pkg);

    if haskell_csyntax.trim() == rust_csyntax.trim() {
        FileResult::ExactMatch
    } else {
        FileResult::CsyntaxDiff {
            haskell: haskell_csyntax,
            rust: rust_csyntax,
        }
    }
}

pub fn get_bsc_path() -> Option<String> {
    std::env::var("BSC_PATH").ok()
}

pub fn get_libraries_dir() -> Option<PathBuf> {
    std::env::var("BSC_LIBRARIES_DIR").ok().map(PathBuf::from)
}

pub fn get_testsuite_dir() -> PathBuf {
    std::env::var("BSC_TESTSUITE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("/root/bsc/testsuite"))
}
