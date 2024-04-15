use self::sstr::Sstr;

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum NumberType {
    Integer,
    Binary,
    Hex,
    Float,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrStatus {
    Valid,
    InvalidEscape,
    InvalidNewline,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrLabelStatus {
    NotString,
    String,
    InvalidEscape,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(align(8))]
pub enum Token<'a> {
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Asterick,
    /// /
    Slash,
    /// %
    Percent,
    /// ^
    Carrot,
    /// &
    Ampersand,
    /// ~
    Tilde,
    /// |
    Pipe,
    /// <<
    LtLt,
    /// >>
    GtGt,
    /// //
    SlashSlash,
    /// ==
    EqEq,
    /// ~=
    TildeEq,
    /// <=
    LtEq,
    /// >=
    GtEq,
    /// <
    Lt,
    /// >
    Gt,
    /// =
    Eq,

    /// (
    LPar,
    /// )
    RPar,
    /// {
    LBrace,
    /// }
    RBrace,
    /// [
    LBracket,
    /// ]
    RBracket,

    /// ,
    Comma,

    Label {
        label: Sstr<'a>,
        raw: bool,
        kind: StrLabelStatus,
    },
    Ident(Sstr<'a>),
    StringLiteral {
        str: Sstr<'a>,
        raw: bool,
        valid: StrStatus,
    },
    CharLiteral {
        str: Sstr<'a>,
        raw: bool,
        valid: StrStatus,
    },
    NumericLiteral {
        str: Sstr<'a>,
        hint: NumberType,
    },
    BooleanLiteral(bool),

    SingleLineComment(Sstr<'a>),
    MultiLineComment(Sstr<'a>),
}

pub enum Kind {
    Message,
    Warning,
    Error(u32),
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Message => write!(f, "{BOLD}message{RESET}"),
            Kind::Warning => write!(f, "{BOLD}{YELLOW}warning{RESET}"),
            Kind::Error(e) => write!(f, "{BOLD}{RED}error[E{}]{RESET}", e),
        }
    }
}

pub struct SpanFmt<'a> {
    pub span: SpanD,
    pub original: &'a str,
    pub message: Option<&'a str>,
    pub kind: Kind,
    pub filename: &'a str,
}

const BOLD: &str = "\x1b[1m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const BLUE: &str = "\x1b[34m";
const GREEN: &str = "\x1b[32m";
const RESET: &str = "\x1b[0;22m";

impl<'a> std::fmt::Display for SpanFmt<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(message) = self.message {
            writeln!(f, "{}{RESET}{BOLD}: {}", self.kind, message)?;
        } else {
            writeln!(f, "{}{RESET}", self.kind)?;
        }

        let line = self.span.line + 1;

        // this is funny
        let space = "                                                                                                                                                                                                                                                                ";
        let space = &space[0..((line as f32).log10().floor() as u8) as usize + 1];

        writeln!(
            f,
            "{BLUE}{BOLD}{space}--> {RESET}{}:{}:{}",
            self.filename,
            line,
            self.span.col + 1
        )?;
        writeln!(f, "{BLUE}{BOLD}{space} |")?;
        writeln!(
            f,
            "{} |{RESET} {}",
            line,
            &self.original[self.span.offset as usize..(self.span.offset + self.span.len) as usize]
        )?;
        writeln!(f, "{BLUE}{BOLD}{space} |{RESET}")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenizerError<'a> {
    InvalidChar(char),
    EmptyCharLiteral,
    UnclosedCharLiteral,
    CharLiteralTooBig,
    UnclosedMultiLineComment,
    InvalidEscape(&'a str),
    UnfinishedEscapeSequence(&'a str),
    UnclosedStringLiteral,
    EmptyExponent,
    InvalidBase2Digit(char),
    NoNumberAfterBasePrefix,
}
