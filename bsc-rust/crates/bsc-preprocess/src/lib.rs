use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum PreprocessError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Undefined macro: `{0}")]
    UndefinedMacro(String),
    #[error("Missing include file: {0}")]
    MissingIncludeFile(String),
    #[error("Unmatched `endif")]
    UnmatchedEndif,
    #[error("Unmatched `else")]
    UnmatchedElse,
    #[error("Invalid `define: {0}")]
    InvalidDefine(String),
    #[error("Wrong number of parameters for macro `{name}`: expected {expected}, got {got}")]
    WrongParamCount {
        name: String,
        expected: usize,
        got: usize,
    },
    #[error("Missing `endif")]
    MissingEndif,
    #[error("No identifier after `{0}")]
    NoIdentifier(String),
}

pub type Result<T> = std::result::Result<T, PreprocessError>;

#[derive(Debug, Clone, Default)]
pub struct PreprocessFlags {
    pub backend: Option<Backend>,
    pub defines: Vec<String>,
    pub include_paths: Vec<PathBuf>,
    pub vpp: bool,
    pub cpp: bool,
}

#[derive(Debug, Clone, Copy)]
pub enum Backend {
    Bluesim,
    Verilog,
}

#[derive(Debug, Clone)]
struct MacroDef {
    params: Vec<String>,
    value: String,
    pos_file: String,
    pos_line: u32,
    pos_col: u32,
}

#[derive(Debug, Clone)]
struct Position {
    file: String,
    line: u32,
    col: u32,
}

impl Position {
    fn new(file: &str) -> Self {
        Position {
            file: file.to_string(),
            line: 1,
            col: 1,
        }
    }

    fn advance(&mut self, c: char) {
        if c == '\n' {
            self.line += 1;
            self.col = 1;
        } else if c == '\t' {
            self.col = ((self.col - 1) / 8 + 1) * 8 + 1;
        } else {
            self.col += 1;
        }
    }

    fn advance_str(&mut self, s: &str) {
        for c in s.chars() {
            self.advance(c);
        }
    }
}

struct Preprocessor {
    env: HashMap<String, MacroDef>,
    include_paths: Vec<PathBuf>,
    current_file: PathBuf,
    includes: Vec<String>,
}

impl Preprocessor {
    fn new(flags: &PreprocessFlags, current_file: &Path) -> Self {
        let mut env = HashMap::new();

        env.insert(
            "bluespec".to_string(),
            MacroDef {
                params: vec![],
                value: "2024.01".to_string(),
                pos_file: "Prelude".to_string(),
                pos_line: 1,
                pos_col: 1,
            },
        );
        env.insert(
            "BLUESPEC".to_string(),
            MacroDef {
                params: vec![],
                value: "2024.01".to_string(),
                pos_file: "Prelude".to_string(),
                pos_line: 1,
                pos_col: 1,
            },
        );

        if let Some(backend) = &flags.backend {
            match backend {
                Backend::Bluesim => {
                    env.insert(
                        "__GENC__".to_string(),
                        MacroDef {
                            params: vec![],
                            value: String::new(),
                            pos_file: "CommandLine".to_string(),
                            pos_line: 1,
                            pos_col: 1,
                        },
                    );
                }
                Backend::Verilog => {
                    env.insert(
                        "__GENVERILOG__".to_string(),
                        MacroDef {
                            params: vec![],
                            value: String::new(),
                            pos_file: "CommandLine".to_string(),
                            pos_line: 1,
                            pos_col: 1,
                        },
                    );
                }
            }
        }

        for def in &flags.defines {
            let (name, value) = if let Some(pos) = def.find('=') {
                (def[..pos].to_string(), def[pos + 1..].to_string())
            } else {
                (def.clone(), String::new())
            };
            env.insert(
                name,
                MacroDef {
                    params: vec![],
                    value,
                    pos_file: "CommandLine".to_string(),
                    pos_line: 1,
                    pos_col: 1,
                },
            );
        }

        Preprocessor {
            env,
            include_paths: flags.include_paths.clone(),
            current_file: current_file.to_path_buf(),
            includes: Vec::new(),
        }
    }

    fn emit_line_pos(&self, pos: &Position, level: u32) -> String {
        format!(
            " `line({},{},{},{})",
            pos.file, pos.line, pos.col, level
        )
    }

    fn emit_line(&self, pos: &Position, level: u32) -> String {
        format!("`line {} \"{}\" {}\n", pos.line, pos.file, level)
    }

    fn preprocess(&mut self, input: &str, init_pos: Position) -> Result<String> {
        let mut output = String::new();
        let chars: Vec<char> = input.chars().collect();
        let mut i = 0;
        let mut pos = init_pos;

        while i < chars.len() {
            if chars[i] == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
                while i < chars.len() && chars[i] != '\n' {
                    output.push(chars[i]);
                    pos.advance(chars[i]);
                    i += 1;
                }
            } else if chars[i] == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
                output.push(chars[i]);
                pos.advance(chars[i]);
                i += 1;
                output.push(chars[i]);
                pos.advance(chars[i]);
                i += 1;
                while i < chars.len() {
                    if chars[i] == '*' && i + 1 < chars.len() && chars[i + 1] == '/' {
                        output.push(chars[i]);
                        pos.advance(chars[i]);
                        i += 1;
                        output.push(chars[i]);
                        pos.advance(chars[i]);
                        i += 1;
                        break;
                    }
                    output.push(chars[i]);
                    pos.advance(chars[i]);
                    i += 1;
                }
            } else if chars[i] == '`' {
                let backtick_pos = pos.clone();
                i += 1;
                pos.advance('`');

                if i >= chars.len() {
                    output.push('`');
                    continue;
                }

                if chars[i] == '"' {
                    output.push('"');
                    i += 1;
                    pos.advance('"');
                    continue;
                }

                if chars[i] == '\\' {
                    i += 1;
                    pos.advance('\\');
                    continue;
                }

                let dir_start = i;
                while i < chars.len() && is_id_char(chars[i]) {
                    i += 1;
                }
                let directive: String = chars[dir_start..i].iter().collect();
                pos.advance_str(&directive);

                match directive.as_str() {
                    "define" => {
                        self.skip_whitespace(&chars, &mut i, &mut pos);
                        let name_start = i;
                        while i < chars.len() && is_id_char(chars[i]) && chars[i] != '(' {
                            i += 1;
                        }
                        let name: String = chars[name_start..i].iter().collect();
                        pos.advance_str(&name);

                        if name.is_empty() {
                            return Err(PreprocessError::NoIdentifier("`define".to_string()));
                        }

                        let mut params = Vec::new();
                        if i < chars.len() && chars[i] == '(' {
                            i += 1;
                            pos.advance('(');
                            let params_str = self.read_until(&chars, &mut i, &mut pos, ')');
                            if i < chars.len() && chars[i] == ')' {
                                i += 1;
                                pos.advance(')');
                            }
                            for p in params_str.split(',') {
                                let p = p.trim().replace('\\', "");
                                if !p.is_empty() {
                                    params.push(p);
                                }
                            }
                        }

                        self.skip_horizontal_whitespace(&chars, &mut i, &mut pos);

                        let value_pos = pos.clone();
                        let value = self.read_define_value(&chars, &mut i, &mut pos);

                        self.env.insert(
                            name,
                            MacroDef {
                                params,
                                value,
                                pos_file: value_pos.file,
                                pos_line: value_pos.line,
                                pos_col: value_pos.col,
                            },
                        );
                        output.push_str(&self.emit_line_pos(&pos, 0));
                    }
                    "undef" => {
                        self.skip_whitespace(&chars, &mut i, &mut pos);
                        let name_start = i;
                        while i < chars.len() && is_id_char(chars[i]) {
                            i += 1;
                        }
                        let name: String = chars[name_start..i].iter().collect();
                        pos.advance_str(&name);

                        if name.is_empty() {
                            return Err(PreprocessError::NoIdentifier("`undef".to_string()));
                        }
                        self.env.remove(&name);
                    }
                    "ifdef" => {
                        self.skip_whitespace(&chars, &mut i, &mut pos);
                        let name_start = i;
                        while i < chars.len() && is_id_char(chars[i]) {
                            i += 1;
                        }
                        let name: String = chars[name_start..i].iter().collect();
                        pos.advance_str(&name);

                        if name.is_empty() {
                            return Err(PreprocessError::NoIdentifier("`ifdef".to_string()));
                        }

                        let defined = self.env.contains_key(&name);
                        let block = self.read_ifdef_block(&chars, &mut i, &mut pos)?;
                        let after_if_pos = pos.clone();

                        let branch_pos = Position::new(&pos.file);
                        let processed = if defined {
                            output.push_str(&self.emit_line_pos(&branch_pos, 0));
                            self.preprocess(&block.then_branch, branch_pos)?
                        } else if let Some(else_branch) = block.else_branch {
                            output.push_str(&self.emit_line_pos(&branch_pos, 0));
                            self.preprocess(&else_branch, branch_pos)?
                        } else {
                            String::new()
                        };
                        output.push_str(&processed);
                        output.push_str(&self.emit_line_pos(&after_if_pos, 0));
                    }
                    "ifndef" => {
                        self.skip_whitespace(&chars, &mut i, &mut pos);
                        let name_start = i;
                        while i < chars.len() && is_id_char(chars[i]) {
                            i += 1;
                        }
                        let name: String = chars[name_start..i].iter().collect();
                        pos.advance_str(&name);

                        if name.is_empty() {
                            return Err(PreprocessError::NoIdentifier("`ifndef".to_string()));
                        }

                        let defined = self.env.contains_key(&name);
                        let block = self.read_ifdef_block(&chars, &mut i, &mut pos)?;
                        let after_if_pos = pos.clone();

                        let branch_pos = Position::new(&pos.file);
                        let processed = if !defined {
                            output.push_str(&self.emit_line_pos(&branch_pos, 0));
                            self.preprocess(&block.then_branch, branch_pos)?
                        } else if let Some(else_branch) = block.else_branch {
                            output.push_str(&self.emit_line_pos(&branch_pos, 0));
                            self.preprocess(&else_branch, branch_pos)?
                        } else {
                            String::new()
                        };
                        output.push_str(&processed);
                        output.push_str(&self.emit_line_pos(&after_if_pos, 0));
                    }
                    "else" | "elsif" | "endif" => {
                        break;
                    }
                    "include" => {
                        self.skip_whitespace(&chars, &mut i, &mut pos);
                        let delim_end = if i < chars.len() && chars[i] == '"' {
                            '"'
                        } else if i < chars.len() && chars[i] == '<' {
                            '>'
                        } else {
                            return Err(PreprocessError::MissingIncludeFile(
                                "no delimiter".to_string(),
                            ));
                        };
                        i += 1;
                        pos.advance(chars[i - 1]);
                        let filename = self.read_until(&chars, &mut i, &mut pos, delim_end);
                        if i < chars.len() && chars[i] == delim_end {
                            i += 1;
                            pos.advance(delim_end);
                        }

                        let (content, resolved_path) = self.read_include_file(&filename)?;
                        self.includes.push(resolved_path.clone());

                        let inc_pos = Position::new(&resolved_path);
                        output.push_str(&self.emit_line(&inc_pos, 1));
                        let processed = self.preprocess(&content, inc_pos)?;
                        output.push_str(&processed);
                        output.push_str(&self.emit_line(&pos, 2));
                    }
                    "line" => {
                        output.push('`');
                        output.push_str("line");
                        while i < chars.len() && chars[i] != '\n' {
                            output.push(chars[i]);
                            pos.advance(chars[i]);
                            i += 1;
                        }
                    }
                    "resetall" => {
                        let includes_backup: Vec<_> = self
                            .env
                            .iter()
                            .filter(|(_, v)| v.pos_file == "Include")
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect();
                        self.env.clear();
                        self.env.insert(
                            "bluespec".to_string(),
                            MacroDef {
                                params: vec![],
                                value: "2024.01".to_string(),
                                pos_file: "Prelude".to_string(),
                                pos_line: 1,
                                pos_col: 1,
                            },
                        );
                        self.env.insert(
                            "BLUESPEC".to_string(),
                            MacroDef {
                                params: vec![],
                                value: "2024.01".to_string(),
                                pos_file: "Prelude".to_string(),
                                pos_line: 1,
                                pos_col: 1,
                            },
                        );
                        for (k, v) in includes_backup {
                            self.env.insert(k, v);
                        }
                    }
                    _ => {
                        if let Some(macro_def) = self.env.get(&directive).cloned() {
                            let macro_pos = Position {
                                file: macro_def.pos_file.clone(),
                                line: macro_def.pos_line,
                                col: macro_def.pos_col,
                            };

                            if macro_def.params.is_empty() {
                                output.push_str(&self.emit_line_pos(&macro_pos, 1));
                                let expanded =
                                    self.preprocess(&macro_def.value, macro_pos.clone())?;
                                output.push_str(&expanded);
                                output.push_str(&self.emit_line_pos(&pos, 2));
                            } else {
                                self.skip_whitespace(&chars, &mut i, &mut pos);
                                if i < chars.len() && chars[i] == '(' {
                                    i += 1;
                                    pos.advance('(');
                                    let args_str = self.read_params(&chars, &mut i, &mut pos);
                                    if i < chars.len() && chars[i] == ')' {
                                        i += 1;
                                        pos.advance(')');
                                    }
                                    let args = self.split_params(&args_str);

                                    if args.len() != macro_def.params.len() {
                                        return Err(PreprocessError::WrongParamCount {
                                            name: directive,
                                            expected: macro_def.params.len(),
                                            got: args.len(),
                                        });
                                    }

                                    let mut value = macro_def.value.clone();
                                    for (param, arg) in macro_def.params.iter().zip(args.iter()) {
                                        value = replace_param(&value, param, arg);
                                    }
                                    value = merge_tokens(&value);

                                    output.push_str(&self.emit_line_pos(&macro_pos, 1));
                                    let expanded = self.preprocess(&value, macro_pos.clone())?;
                                    output.push_str(&expanded);
                                    output.push_str(&self.emit_line_pos(&pos, 2));
                                } else {
                                    return Err(PreprocessError::WrongParamCount {
                                        name: directive,
                                        expected: macro_def.params.len(),
                                        got: 0,
                                    });
                                }
                            }
                        } else {
                            return Err(PreprocessError::UndefinedMacro(directive));
                        }
                    }
                }
            } else {
                output.push(chars[i]);
                pos.advance(chars[i]);
                i += 1;
            }
        }

        Ok(output)
    }

    fn skip_whitespace(&self, chars: &[char], i: &mut usize, pos: &mut Position) {
        while *i < chars.len() && chars[*i].is_whitespace() {
            pos.advance(chars[*i]);
            *i += 1;
        }
    }

    fn skip_horizontal_whitespace(&self, chars: &[char], i: &mut usize, pos: &mut Position) {
        while *i < chars.len() && (chars[*i] == ' ' || chars[*i] == '\t') {
            pos.advance(chars[*i]);
            *i += 1;
        }
    }

    fn read_until(&self, chars: &[char], i: &mut usize, pos: &mut Position, delim: char) -> String {
        let mut result = String::new();
        while *i < chars.len() && chars[*i] != delim {
            result.push(chars[*i]);
            pos.advance(chars[*i]);
            *i += 1;
        }
        result
    }

    fn read_params(&self, chars: &[char], i: &mut usize, pos: &mut Position) -> String {
        let mut result = String::new();
        let mut depth = 1;
        while *i < chars.len() && depth > 0 {
            if chars[*i] == '(' {
                depth += 1;
            } else if chars[*i] == ')' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            result.push(chars[*i]);
            pos.advance(chars[*i]);
            *i += 1;
        }
        result
    }

    fn split_params(&self, s: &str) -> Vec<String> {
        let mut result = Vec::new();
        let mut current = String::new();
        let mut depth = 0;
        let chars: Vec<char> = s.chars().collect();
        let mut i = 0;

        while i < chars.len() {
            if chars[i] == '`'
                && i + 5 < chars.len()
                && &s[i..i + 5] == "`line"
                && (i + 5 >= chars.len()
                    || chars[i + 5] == '('
                    || chars[i + 5].is_whitespace())
            {
                current.push_str("`line");
                i += 5;
                if i < chars.len() && chars[i] == '(' {
                    current.push('(');
                    i += 1;
                    while i < chars.len() && chars[i] != ')' {
                        current.push(chars[i]);
                        i += 1;
                    }
                    if i < chars.len() {
                        current.push(')');
                        i += 1;
                    }
                }
                continue;
            }
            if chars[i] == '(' {
                depth += 1;
                current.push(chars[i]);
            } else if chars[i] == ')' {
                depth -= 1;
                current.push(chars[i]);
            } else if chars[i] == ',' && depth == 0 {
                result.push(current.trim().to_string());
                current = String::new();
            } else {
                current.push(chars[i]);
            }
            i += 1;
        }
        if !current.is_empty() || !result.is_empty() {
            result.push(current.trim().to_string());
        }
        result
    }

    fn read_define_value(&self, chars: &[char], i: &mut usize, pos: &mut Position) -> String {
        let mut value = String::new();
        while *i < chars.len() {
            if chars[*i] == '\n' {
                pos.advance('\n');
                *i += 1;
                break;
            } else if chars[*i] == '\\'
                && *i + 1 < chars.len()
                && (chars[*i + 1] == '\n' || chars[*i + 1] == '\r')
            {
                if chars[*i + 1] == '\r' && *i + 2 < chars.len() && chars[*i + 2] == '\n' {
                    value.push('\n');
                    pos.advance('\\');
                    pos.advance('\r');
                    pos.advance('\n');
                    *i += 3;
                } else {
                    value.push('\n');
                    pos.advance('\\');
                    pos.advance(chars[*i + 1]);
                    *i += 2;
                }
            } else if chars[*i] == '/' && *i + 1 < chars.len() && chars[*i + 1] == '/' {
                while *i < chars.len() && chars[*i] != '\n' {
                    pos.advance(chars[*i]);
                    *i += 1;
                }
                if *i < chars.len() {
                    pos.advance('\n');
                    *i += 1;
                }
                break;
            } else if chars[*i] == '/' && *i + 1 < chars.len() && chars[*i + 1] == '*' {
                value.push(chars[*i]);
                pos.advance(chars[*i]);
                *i += 1;
                value.push(chars[*i]);
                pos.advance(chars[*i]);
                *i += 1;
                while *i < chars.len() {
                    if chars[*i] == '*' && *i + 1 < chars.len() && chars[*i + 1] == '/' {
                        value.push(chars[*i]);
                        pos.advance(chars[*i]);
                        *i += 1;
                        value.push(chars[*i]);
                        pos.advance(chars[*i]);
                        *i += 1;
                        break;
                    }
                    value.push(chars[*i]);
                    pos.advance(chars[*i]);
                    *i += 1;
                }
            } else {
                value.push(chars[*i]);
                pos.advance(chars[*i]);
                *i += 1;
            }
        }
        value.trim_end().to_string()
    }

    fn read_ifdef_block(
        &self,
        chars: &[char],
        i: &mut usize,
        pos: &mut Position,
    ) -> Result<IfdefBlock> {
        let mut then_branch = String::new();
        let mut else_branch: Option<String> = None;
        let mut depth = 1;

        while *i < chars.len() && depth > 0 {
            if chars[*i] == '`' {
                let start = *i;
                *i += 1;
                pos.advance('`');
                let dir_start = *i;
                while *i < chars.len() && is_id_char(chars[*i]) {
                    *i += 1;
                }
                let dir: String = chars[dir_start..*i].iter().collect();
                pos.advance_str(&dir);

                match dir.as_str() {
                    "ifdef" | "ifndef" => {
                        depth += 1;
                        if else_branch.is_some() {
                            else_branch.as_mut().unwrap().push('`');
                            else_branch.as_mut().unwrap().push_str(&dir);
                        } else {
                            then_branch.push('`');
                            then_branch.push_str(&dir);
                        }
                    }
                    "endif" => {
                        depth -= 1;
                        if depth > 0 {
                            if else_branch.is_some() {
                                else_branch.as_mut().unwrap().push('`');
                                else_branch.as_mut().unwrap().push_str(&dir);
                            } else {
                                then_branch.push('`');
                                then_branch.push_str(&dir);
                            }
                        }
                    }
                    "else" if depth == 1 => {
                        else_branch = Some(String::new());
                    }
                    "elsif" if depth == 1 => {
                        let rest: String = chars[start..].iter().collect();
                        let elsif_as_ifdef = format!("`ifdef{}", &rest[6..]);
                        else_branch = Some(elsif_as_ifdef);
                        while *i < chars.len() {
                            if chars[*i] == '`' {
                                let peek_start = *i + 1;
                                let mut peek_end = peek_start;
                                while peek_end < chars.len() && is_id_char(chars[peek_end]) {
                                    peek_end += 1;
                                }
                                let peek_dir: String =
                                    chars[peek_start..peek_end].iter().collect();
                                if peek_dir == "endif" {
                                    if depth == 1 {
                                        pos.advance('`');
                                        pos.advance_str(&peek_dir);
                                        *i = peek_end;
                                        depth = 0;
                                        break;
                                    } else {
                                        depth -= 1;
                                    }
                                } else if peek_dir == "ifdef" || peek_dir == "ifndef" {
                                    depth += 1;
                                }
                            }
                            pos.advance(chars[*i]);
                            *i += 1;
                        }
                        break;
                    }
                    _ => {
                        if else_branch.is_some() {
                            else_branch.as_mut().unwrap().push('`');
                            else_branch.as_mut().unwrap().push_str(&dir);
                        } else {
                            then_branch.push('`');
                            then_branch.push_str(&dir);
                        }
                    }
                }
            } else {
                if let Some(ref mut eb) = else_branch {
                    eb.push(chars[*i]);
                } else {
                    then_branch.push(chars[*i]);
                }
                pos.advance(chars[*i]);
                *i += 1;
            }
        }

        Ok(IfdefBlock {
            then_branch,
            else_branch,
        })
    }

    fn read_include_file(&self, filename: &str) -> Result<(String, String)> {
        if let Ok(content) = fs::read_to_string(filename) {
            return Ok((content, filename.to_string()));
        }

        if let Some(parent) = self.current_file.parent() {
            let path = parent.join(filename);
            if let Ok(content) = fs::read_to_string(&path) {
                return Ok((content, path.to_string_lossy().to_string()));
            }
        }

        for inc_path in &self.include_paths {
            let path = inc_path.join(filename);
            if let Ok(content) = fs::read_to_string(&path) {
                return Ok((content, path.to_string_lossy().to_string()));
            }
        }

        Err(PreprocessError::MissingIncludeFile(filename.to_string()))
    }
}

struct IfdefBlock {
    then_branch: String,
    else_branch: Option<String>,
}

fn is_id_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '$'
}

fn is_id_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn replace_param(value: &str, param: &str, arg: &str) -> String {
    let mut result = String::new();
    let chars: Vec<char> = value.chars().collect();
    let param_chars: Vec<char> = param.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if is_id_start(chars[i]) {
            let start = i;
            while i < chars.len() && is_id_char(chars[i]) {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            if word == param {
                result.push_str(arg);
            } else {
                result.push_str(&word);
            }
        } else {
            result.push(chars[i]);
            i += 1;
        }
    }
    result
}

fn merge_tokens(value: &str) -> String {
    let mut result = String::new();
    let chars: Vec<char> = value.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if chars[i] == '`' && i + 1 < chars.len() && chars[i + 1] == '`' {
            if i > 0 && result.ends_with(char::is_whitespace) {
                while result.ends_with(char::is_whitespace) {
                    result.pop();
                }
            }
            i += 2;
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }
            if i + 5 <= chars.len() && &value[i..i + 5] == "`line" {
                while i < chars.len() && chars[i] != ')' {
                    i += 1;
                }
                if i < chars.len() {
                    i += 1;
                }
            }
        } else {
            result.push(chars[i]);
            i += 1;
        }
    }
    result
}

fn cpp_line_to_sv_line(line: &str) -> String {
    let trimmed = line.trim_start();
    if !trimmed.starts_with('#') {
        return line.to_string();
    }

    let rest = trimmed[1..].trim_start();
    let rest = if rest.starts_with("line") {
        rest[4..].trim_start()
    } else {
        rest
    };

    let mut parts = rest.splitn(2, char::is_whitespace);
    if let Some(line_num) = parts.next() {
        if line_num.chars().all(|c| c.is_ascii_digit()) {
            if let Some(filename) = parts.next() {
                let filename = filename.trim();
                if filename.starts_with('"') {
                    return format!("`line {} {}", line_num, filename);
                }
            }
        }
    }
    line.to_string()
}

pub fn preprocess(source_path: &Path, flags: &PreprocessFlags) -> Result<String> {
    let source = fs::read_to_string(source_path)?;
    preprocess_string(&source, &source_path.to_string_lossy(), flags)
}

pub fn preprocess_string(source: &str, filename: &str, flags: &PreprocessFlags) -> Result<String> {
    let source = if flags.cpp {
        source
            .lines()
            .map(cpp_line_to_sv_line)
            .collect::<Vec<_>>()
            .join("\n")
    } else {
        source.to_string()
    };

    if !flags.vpp {
        return Ok(source);
    }

    let mut preprocessor = Preprocessor::new(flags, Path::new(filename));
    let init_pos = Position::new(filename);
    let result = preprocessor.preprocess(&source, init_pos)?;

    Ok(result)
}

pub fn get_includes(source_path: &Path, flags: &PreprocessFlags) -> Result<Vec<String>> {
    let source = fs::read_to_string(source_path)?;
    let mut preprocessor = Preprocessor::new(flags, source_path);
    let init_pos = Position::new(&source_path.to_string_lossy());
    let _ = preprocessor.preprocess(&source, init_pos)?;
    Ok(preprocessor.includes)
}
