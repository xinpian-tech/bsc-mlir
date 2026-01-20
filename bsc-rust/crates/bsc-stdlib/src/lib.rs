//! Standard library loader for BSC.
//!
//! Parses and loads the Bluespec stdlib .bs source files from src/Libraries/.

use std::path::{Path, PathBuf};

use bsc_symtab::SymTab;

/// Loader for BSC standard library files.
///
/// Handles loading and parsing of Prelude and other stdlib modules
/// from the src/Libraries/ directory in the BSC source tree.
#[derive(Debug, Clone)]
pub struct StdlibLoader {
    /// Path to the Libraries directory (e.g., src/Libraries)
    libraries_dir: PathBuf,
}

/// Errors that can occur when loading the standard library.
#[derive(Debug, thiserror::Error)]
pub enum StdlibError {
    /// Libraries directory not found.
    #[error("Libraries directory not found: {0}")]
    LibrariesDirNotFound(PathBuf),

    /// Failed to read a stdlib file from disk.
    #[error("Failed to read stdlib file {path}: {source}")]
    IoError {
        /// Path to the file that could not be read.
        path: PathBuf,
        /// The underlying I/O error.
        source: std::io::Error,
    },

    /// Failed to parse a stdlib file.
    #[error("Failed to parse stdlib file {path}: {message}")]
    ParseError {
        /// Path to the file that failed to parse.
        path: PathBuf,
        /// Description of the parse error.
        message: String,
    },
}

/// Core stdlib directories in order of priority.
const STDLIB_DIRS: &[&str] = &["Base1", "Base2", "Base3-Contexts", "Base3-Math", "Base3-Misc"];

impl StdlibLoader {
    /// Create a new loader with explicit path to src/Libraries.
    ///
    /// # Arguments
    ///
    /// * `libraries_dir` - Path to the Libraries directory (e.g., src/Libraries)
    ///
    /// # Errors
    ///
    /// Returns error if the directory does not exist.
    pub fn new(libraries_dir: PathBuf) -> Result<Self, StdlibError> {
        if !libraries_dir.exists() {
            return Err(StdlibError::LibrariesDirNotFound(libraries_dir));
        }
        Ok(Self { libraries_dir })
    }

    /// Get the search paths for imports.
    ///
    /// Returns the standard search paths used when resolving imports:
    /// - `$LIBRARIES_DIR/Base1`
    /// - `$LIBRARIES_DIR/Base2`
    /// - etc.
    #[must_use]
    pub fn search_paths(&self) -> Vec<PathBuf> {
        STDLIB_DIRS
            .iter()
            .map(|dir| self.libraries_dir.join(dir))
            .filter(|p| p.exists())
            .collect()
    }

    /// Load and parse the Prelude, returning its symbol table.
    ///
    /// This loads Prelude.bs from Base1 and returns its symbol table.
    ///
    /// # Errors
    ///
    /// Returns an error if Prelude.bs cannot be read or parsed.
    pub fn load_prelude(&self) -> Result<SymTab, StdlibError> {
        self.load_module("Prelude")
    }

    /// Load a specific stdlib module by name.
    ///
    /// Searches for the module in the standard search paths and parses it.
    ///
    /// # Arguments
    ///
    /// * `name` - The module name (e.g., "Vector", "FIFO", "Prelude").
    ///
    /// # Errors
    ///
    /// Returns an error if the module cannot be found, read, or parsed.
    pub fn load_module(&self, name: &str) -> Result<SymTab, StdlibError> {
        let file_name = format!("{name}.bs");

        // Search in standard paths
        for search_path in self.search_paths() {
            let path = search_path.join(&file_name);
            if path.exists() {
                return self.parse_file(&path);
            }
        }

        Err(StdlibError::IoError {
            path: PathBuf::from(&file_name),
            source: std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("Module '{name}' not found in search paths"),
            ),
        })
    }

    /// Parse a file and return its symbol table.
    fn parse_file(&self, path: &Path) -> Result<SymTab, StdlibError> {
        let source = std::fs::read_to_string(path).map_err(|source| StdlibError::IoError {
            path: path.to_path_buf(),
            source,
        })?;

        // TODO: Use bsc_parser_classic to parse the source
        // For now, return an empty symbol table as a placeholder
        let _ = source;

        // Placeholder: actual parsing will be implemented when
        // bsc-parser-classic is complete
        Ok(SymTab::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_search_paths() {
        // This test uses a mock path that doesn't exist
        let loader = StdlibLoader {
            libraries_dir: PathBuf::from("/mock/Libraries"),
        };
        // Since the paths don't exist, search_paths returns empty
        let paths = loader.search_paths();
        assert!(paths.is_empty());
    }
}
