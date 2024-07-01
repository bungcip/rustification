use colored::Colorize;

use fern::colors::ColoredLevelConfig;
use log::{Level, SetLoggerError};
use std::collections::HashSet;
use std::fmt::{self, Display};
use std::io;
use std::str::FromStr;
use strum_macros::{Display, EnumString};

use crate::c_ast::{ClangAstParseErrorKind, DisplaySrcSpan};
use c2rust_ast_exporter::get_clang_major_version;

const DEFAULT_WARNINGS: &[Diagnostic] = &[Diagnostic::ClangAst];

#[derive(PartialEq, Eq, Hash, Debug, Display, EnumString, Clone)]
#[strum(serialize_all = "kebab-case")]
pub enum Diagnostic {
    All,
    Comments,
    ClangAst,
}

macro_rules! diag {
    ($type:path, $($arg:tt)*) => (log::warn!(target: &$type.to_string(), $($arg)*))
}

pub(crate) use diag;

pub fn init(mut enabled_warnings: HashSet<Diagnostic>, log_level: log::LevelFilter) {
    enabled_warnings.extend(DEFAULT_WARNINGS.iter().cloned());

    let colors = ColoredLevelConfig::new();
    let (max_level, logger) = fern::Dispatch::new()
        .format(move |out, message, record| {
            let level_label = match record.level() {
                Level::Error => "error",
                Level::Warn => "warning",
                Level::Info => "info",
                Level::Debug => "debug",
                Level::Trace => "trace",
            };
            let target = record.target();
            let warn_flag = Diagnostic::from_str(target)
                .map(|_| format!(" [-W{}]", target))
                .unwrap_or_default();
            out.finish(format_args!(
                "\x1B[{}m{}:\x1B[0m {}{}",
                colors.get_color(&record.level()).to_fg_str(),
                level_label,
                message,
                warn_flag,
            ))
        })
        .level(log_level)
        .filter(move |metadata| {
            if enabled_warnings.contains(&Diagnostic::All) {
                return true;
            }
            Diagnostic::from_str(metadata.target())
                .map(|d| enabled_warnings.contains(&d))
                .unwrap_or(true)
        })
        .chain(io::stderr())
        .into_log();
    // Ignore the [`SetLoggerError`] b/c we just want to make sure it's set at least once.
    let _: Result<(), SetLoggerError> = log_reroute::init();
    log_reroute::reroute_boxed(logger);
    log::set_max_level(max_level);
}

#[derive(Debug, Clone)]
pub struct TranslationError {
    pub loc: Option<Vec<DisplaySrcSpan>>,
    pub inner: TranslationErrorKind,
    pub message: String,
}

pub type TranslationResult<T> = Result<T, Box<TranslationError>>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TranslationErrorKind {
    Generic,

    // Not enough simd intrinsics are available in LLVM < 7
    OldLLVMSimd,

    // We are waiting for va_copy support to land in rustc
    VaCopyNotImplemented,

    // Clang AST exported by AST-exporter was not valid
    InvalidClangAst(ClangAstParseErrorKind),
}

/// Constructs a `TranslationError` using the standard string interpolation syntax.
#[macro_export]
macro_rules! generic_loc_err {
    ($loc:expr, $($arg:tt)*) => {
        Box::new(TranslationError {
            loc: if let Some(loc) = $loc { Some(vec![loc]) } else { None },
            inner: $crate::diagnostics::TranslationErrorKind::Generic,
            message: format!($($arg)*),
        })
    }
}

#[macro_export]
macro_rules! generic_err {
    ($message: literal) => {
        Box::new(TranslationError {
            loc: None,
            inner: $crate::diagnostics::TranslationErrorKind::Generic,
            message: $message.into(),
        })
    };

    ($($arg:tt)*) => {
        Box::new(TranslationError {
            loc: None,
            inner: $crate::diagnostics::TranslationErrorKind::Generic,
            message: format!($($arg)*),
        })
    }
}

#[macro_export]
macro_rules! clang_err {
    ($loc:expr, $kind:expr, $($arg:tt)*) => {
        Box::new(TranslationError {
            loc: if let Some(loc) = $loc { Some(vec![loc]) } else { None },
            inner: $crate::diagnostics::TranslationErrorKind::InvalidClangAst($kind),
            message: format!($($arg)*),
        })
    }
}

#[macro_export]
macro_rules! old_llvm_simd_err {
    ($loc:expr, $message: expr) => {
        Box::new(TranslationError {
            loc: if let Some(loc) = $loc {
                Some(vec![loc])
            } else {
                None
            },
            inner: $crate::diagnostics::TranslationErrorKind::OldLLVMSimd,
            message: $message,
        })
    };
}

impl Display for TranslationErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TranslationErrorKind::*;
        match self {
            Generic => {}
            OldLLVMSimd => {
                if let Some(version) = get_clang_major_version() {
                    if version < 7 {
                        return write!(f, "SIMD intrinsics require LLVM 7 or newer. Please build C2Rust against a newer LLVM version.");
                    }
                }
            }

            VaCopyNotImplemented => {
                return write!(f, "Rust does not yet support a C-compatible va_copy which is required to translate this function. See https://github.com/rust-lang/rust/pull/59625");
            }

            InvalidClangAst(_) => {
                return write!(f, "Exported Clang AST was invalid. Check warnings above for unimplemented features.");
            }
        }
        Ok(())
    }
}

impl Display for TranslationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            TranslationErrorKind::Generic => {}
            ref kind => writeln!(f, "{}", kind)?,
        }

        if let Some(loc) = &self.loc {
            for item in loc {
                writeln!(f, "{} {}", "-->".blue(), item)?;
            }
        }
        Ok(())
    }
}

impl TranslationError {
    pub fn new(loc: Option<DisplaySrcSpan>, inner: TranslationErrorKind, message: String) -> Self {
        let loc = loc.map(|loc| vec![loc]);

        Self {
            loc,
            inner,
            message,
        }
    }

    pub fn generic(msg: &'static str) -> Self {
        msg.into()
    }

    pub fn add_loc(mut self, loc: Option<DisplaySrcSpan>) -> Self {
        match (&mut self.loc, loc) {
            (None, Some(x)) => self.loc = Some(vec![x]),
            (Some(ref mut vec), Some(x)) => vec.push(x),
            _ => {}
        }

        self
    }
}

impl From<&'static str> for TranslationError {
    fn from(msg: &'static str) -> Self {
        TranslationError {
            loc: None,
            inner: TranslationErrorKind::Generic,
            message: msg.to_owned(),
        }
    }
}

impl From<TranslationErrorKind> for TranslationError {
    fn from(kind: TranslationErrorKind) -> Self {
        TranslationError {
            loc: None,
            inner: kind,
            message: String::new(),
        }
    }
}
