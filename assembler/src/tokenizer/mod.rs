use std::{iter::Peekable, str::Chars};

use crate::tokenizer::token::NumberType;

use self::token::Token;

pub mod sstr;
pub mod token;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    offset: usize,
    line: usize,
    col: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span<T> {
    pub span: SpanD,
    pub val: T,
}

impl<T> Span<T> {
    pub fn new(val: T, span: SpanD) -> Self {
        Self { val, span }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct SpanD {
    pub line: u32,
    pub col: u32,
    pub offset: u32,
    pub len: u32,
}

impl SpanD {
    pub(super) fn start_end(start: Position, end: Position) -> Self {
        SpanD {
            line: start.line as u32,
            col: start.col as u32,
            offset: start.offset as u32,
            len: (end.offset - start.offset) as u32,
        }
    }

    fn start_size(start: Position, len: u32) -> Self {
        Self {
            line: start.line as u32,
            col: start.col as u32,
            offset: start.offset as u32,
            len,
        }
    }

    pub fn extend_range(&self, other: &Self) -> Self {
        let start_of = self.offset.min(other.offset);
        let end = (self.offset + self.len).max(other.offset + other.len);
        let (line, col) = if self.line < other.line {
            (self.line, self.col)
        } else if self.line > other.line {
            (other.line, other.col)
        } else {
            (self.line, self.col.min(other.col))
        };
        Self {
            line,
            col,
            offset: start_of,
            len: end - start_of,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    // MalformedString(byteyarn::YarnBox<'a, str>),
    ParseIntError(std::num::ParseIntError),
    ParseFloatError(std::num::ParseFloatError),
    IntegerTooLargeError,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrStatus {
    Valid,
    InvalidEscape,
    InvalidNewline,
}

type TokenizerResult<'a> = Result<Span<Token<'a>>, Box<Span<TokenizerError<'a>>>>;

pub struct Tokenizer<'a> {
    str: &'a str,
    chars: Peekable<Chars<'a>>,
    state: State,

    start: Position,
    current: Position,
    escape_start: Position,

    str_status: StrStatus,

    include_comments: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StringInformation(u8);
impl StringInformation{
    pub fn is_string(&self) -> bool{
        self.0 & 0b1 > 0
    }

    pub fn is_char(&self) -> bool{
        !self.is_string()
    }

    pub fn is_raw(&self) -> bool{
        self.0 & 0b10 > 0
    }

    pub fn string() -> Self{
        Self(0b1)
    }

    pub fn char() -> Self{
        Self(0b0)
    }

    pub fn raw_string() -> Self{
        Self(0b11)
    }

    pub fn raw_char() -> Self{
        Self(0b10)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Default,

    String(StringInformation),
    Eof,
    Eq,
    Gt,
    Lt,
    Dot,
    DotDot,
    Ident,
    SingleLineCommentSemi,
    SingleLineComment,
    MultiLineComment,
    MultiLineCommentStar,
    StringEscape(StringInformation),

    NumericStartZero,
    NumericStart,
    NumericDecimal,
    NumericDecimalNumberE,
    NumericDecimalNumberENumber,
    NumericBinStart,
    NumericHexStart,
    NumericDecimalNumberEPM,
    NumericBin,
    NumericHex,
    Slash,
    B,
    StringByteEscape1(StringInformation),
    StringByteEscape2(StringInformation),
}

fn ident(ident: &str) -> Token {
    match ident {
        o => Token::Ident(o.into()),
    }
}

impl<'a> Tokenizer<'a> {
    pub fn new(str: &'a str) -> Self {
        Self {
            str,
            chars: str.chars().peekable(),
            state: State::Default,
            start: Position::default(),
            current: Position::default(),
            escape_start: Position::default(),
            include_comments: false,
            str_status: StrStatus::Valid,
        }
    }

    pub fn with_start(mut self, position: Position) -> Self{
        self.start = position;
        self.current = position;
        self
    }

    pub fn include_comments(mut self) -> Self {
        self.include_comments = true;
        self
    }
}

impl<'a> std::iter::Iterator for Tokenizer<'a> {
    type Item = TokenizerResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut ret = None;
        let mut ret_meta = None;
        let mut update_start_on_error = true;

        let ok_ret_state = State::Default;
        let mut err_ret_state = State::Default;

        loop {
            let c = self.chars.peek().copied();
            let mut consume = true;

            let processing = if let Some(char) = c {
                let mut tmp = self.current;
                tmp.offset += char.len_utf8();
                if char == '\n' {
                    tmp.line += 1;
                    tmp.col = 0;
                } else {
                    tmp.col += 1;
                }
                tmp
            } else {
                self.current
            };

            macro_rules! eof_none {
                ($expr:expr) => {
                    if let Some(char) = $expr {
                        char
                    } else {
                        self.state = State::Eof;
                        return None;
                    }
                };
            }

            macro_rules! unconsume_ret {
                ($sel:ident, $expr:expr) => {{
                    consume = false;
                    ret = Some($expr);
                }};
            }

            match self.state {
                State::Default => match eof_none!(c) {
                    '=' => self.state = State::Eq,
                    '>' => self.state = State::Gt,
                    '<' => self.state = State::Lt,
                    '/' => self.state = State::Slash,
                    '"' => {
                        self.str_status = StrStatus::Valid;
                        self.state = State::String(StringInformation::string())
                    }
                    '\'' => {
                        self.str_status = StrStatus::Valid;
                        self.state = State::String(StringInformation::char())
                    }
                    '.' => self.state = State::Dot,
                    'b' => self.state = State::B,

                    ':' => ret = Some(Ok(Token::Colon)),
                    '+' => ret = Some(Ok(Token::Plus)),
                    '-' => ret = Some(Ok(Token::Minus)),
                    '*' => ret = Some(Ok(Token::Asterick)),
                    '%' => ret = Some(Ok(Token::Percent)),
                    '^' => ret = Some(Ok(Token::Carrot)),
                    '#' => ret = Some(Ok(Token::Octothorp)),
                    '&' => ret = Some(Ok(Token::Ampersand)),
                    '|' => ret = Some(Ok(Token::Pipe)),

                    ',' => ret = Some(Ok(Token::Comma)),
                    ';' => self.state = State::SingleLineCommentSemi,

                    '(' => ret = Some(Ok(Token::LPar)),
                    ')' => ret = Some(Ok(Token::RPar)),
                    '{' => ret = Some(Ok(Token::LBrace)),
                    '}' => ret = Some(Ok(Token::RBrace)),
                    ']' => ret = Some(Ok(Token::RBracket)),
                    '[' => ret = Some(Ok(Token::LBracket)),

                    '0' => {
                        self.state = State::NumericStartZero;
                    }
                    '1'..='9' => {
                        self.state = State::NumericStart;
                    }

                    c if c.is_whitespace() => self.start = processing,
                    '_' | '?' => self.state = State::Ident,
                    c if c.is_alphabetic() => self.state = State::Ident,

                    c => ret = Some(Err(TokenizerError::InvalidChar(c))),
                },
                State::B => match c {
                    Some('"') => {
                        self.str_status = StrStatus::Valid;
                        self.state = State::String(StringInformation::raw_string())
                    }
                    Some('\'') => {
                        self.str_status = StrStatus::Valid;
                        self.state = State::String(StringInformation::raw_char())
                    }
                    _ => {
                        consume = false;
                        self.state = State::Ident;
                    }
                },
                State::Ident => match c {
                    Some('.' | '_' | '?' | '$' | '#' | '@') => {}
                    Some(c) if c.is_alphanumeric() => {}
                    Some(':') => ret = Some(Ok(Token::Label(self.str[self.start.offset..self.current.offset-1].into()))),
                    _ => unconsume_ret!(
                        self,
                        Ok(ident(&self.str[self.start.offset..self.current.offset]))
                    ),
                },
                State::Eq => match c {
                    Some('=') => ret = Some(Ok(Token::EqEq)),
                    _ => unconsume_ret!(self, Ok(Token::Eq)),
                },
                State::Gt => match c {
                    Some('=') => ret = Some(Ok(Token::GtEq)),
                    Some('>') => ret = Some(Ok(Token::GtGt)),
                    _ => unconsume_ret!(self, Ok(Token::Gt)),
                },
                State::Lt => match c {
                    Some('=') => ret = Some(Ok(Token::LtEq)),
                    Some('<') => ret = Some(Ok(Token::LtLt)),
                    _ => unconsume_ret!(self, Ok(Token::Lt)),
                },
                State::Slash => match c {
                    Some('/') => self.state = State::SingleLineComment,
                    Some('*') => self.state = State::MultiLineComment,
                    _ => unconsume_ret!(self, Ok(Token::Slash)),
                },
                State::Dot => match c {
                    Some('.') => self.state = State::DotDot,
                    _ => unconsume_ret!(self, Ok(Token::Dot)),
                },
                State::DotDot => match c {
                    Some('.') => ret = Some(Ok(Token::DotDotDot)),
                    _ => unconsume_ret!(self, Ok(Token::DotDot)),
                },
                State::MultiLineComment => match c {
                    None => ret = Some(Err(TokenizerError::UnclosedMultiLineComment)),
                    Some('*') => self.state = State::MultiLineCommentStar,
                    _ => {}
                },
                State::MultiLineCommentStar => match c {
                    None => ret = Some(Err(TokenizerError::UnclosedMultiLineComment)),
                    Some('/') => {
                        ret = Some(Ok(Token::MultiLineComment(
                            self.str[self.start.offset + 2..self.current.offset - 2].into(),
                        )))
                    },
                    _ => {
                        consume = false;
                        self.state = State::MultiLineComment;
                    }
                },
                State::SingleLineCommentSemi => match c {
                    Some('\n') | None => {
                        ret = Some(Ok(Token::SingleLineComment(
                            self.str[self.start.offset + ';'.len_utf8()..self.current.offset]
                                .into(),
                        )))
                    }
                    _ => {}
                },
                State::SingleLineComment => match c {
                    Some('\n') | None => {
                        ret = Some(Ok(Token::SingleLineComment(
                            self.str[self.start.offset + 2 * '/'.len_utf8()..self.current.offset]
                                .into(),
                        )))
                    }
                    _ => {}
                },
                State::String(str_kind) => match c {
                    Some('\'') if str_kind.is_char() => {
                        let off = if str_kind.is_raw() {2}else{1};
                        let str = self.str[self.start.offset+off..self.current.offset].into();
                        ret = Some(Ok(Token::CharLiteral{ str, raw: str_kind.is_raw(), valid: self.str_status }));
                    } 
                    Some('"') if str_kind.is_string() => {    
                        let off = if str_kind.is_raw() {2}else{1};
                        let str = self.str[self.start.offset+off..self.current.offset].into();
                        ret = Some(Ok(Token::StringLiteral{ str, raw: str_kind.is_raw(), valid: self.str_status }));
                    } 
                    Some('\n') if str_kind.is_char() => {
                        self.str_status = StrStatus::InvalidNewline;
                    }
                    Some('\\') => {
                        self.escape_start = self.current;
                        self.state = State::StringEscape(str_kind);
                    }
                    Some(_) => {},
                    None => ret = Some(Err(TokenizerError::UnclosedStringLiteral)),
                },
                State::StringEscape(kind) => match c {
                    Some('0')
                    | Some('n')
                    | Some('r')
                    | Some('t')
                    | Some('\\')
                    | Some('\'')
                    | Some('"') => self.state = State::String(kind),
                    Some('x') => {
                        self.state = State::StringByteEscape1(kind);
                    }
                    Some(_) => {
                        consume = false;
                        err_ret_state = State::String(kind);
                        update_start_on_error = false;
                        self.str_status = StrStatus::InvalidEscape;
                        ret_meta = Some(SpanD::start_end(self.escape_start, processing));
                        ret = Some(Err(TokenizerError::InvalidEscape(
                            &self.str[self.escape_start.offset..processing.offset],
                        )))
                    }
                    None => {
                        err_ret_state = State::Eof;
                        ret = Some(Err(TokenizerError::UnfinishedEscapeSequence(
                            &self.str[self.start.offset+1..processing.offset],
                        )))
                    }
                },
                State::StringByteEscape1(kind) => match c{
                    Some('a'..='f'|'A'..='F'|'0'..='9') => {
                        if !kind.is_raw() && matches!(c, Some('0'..='7')){
                            self.state = State::StringByteEscape2(kind);
                        }else{
                            err_ret_state = State::StringByteEscape2(kind);
                            update_start_on_error = false;
                            self.str_status = StrStatus::InvalidEscape;
                            ret_meta = Some(SpanD::start_end(self.escape_start, processing));
                            ret = Some(Err(TokenizerError::InvalidEscape(
                                &self.str[self.escape_start.offset..processing.offset],
                            )))
                        }
                    }
                    Some(_) => {
                        err_ret_state = State::StringByteEscape2(kind);
                        update_start_on_error = false;
                        self.str_status = StrStatus::InvalidEscape;
                        ret_meta = Some(SpanD::start_end(self.escape_start, processing));
                        ret = Some(Err(TokenizerError::InvalidEscape(
                            &self.str[self.escape_start.offset..processing.offset],
                        )))
                    }
                    None => {
                        err_ret_state = State::Eof;
                        ret = Some(Err(TokenizerError::UnfinishedEscapeSequence(
                            &self.str[self.escape_start.offset..processing.offset],
                        )))
                    }
                },
                State::StringByteEscape2(kind) => match c{
                    Some('a'..='f'|'A'..='F'|'0'..='9') => {
                        self.state = State::String(kind);
                    }
                    Some(_) => {
                        err_ret_state = State::String(kind);
                        update_start_on_error = false;
                        self.str_status = StrStatus::InvalidEscape;
                        ret_meta = Some(SpanD::start_end(self.escape_start, processing));
                        ret = Some(Err(TokenizerError::InvalidEscape(
                            &self.str[self.escape_start.offset..processing.offset],
                        )))
                    }
                    None => {
                        err_ret_state = State::Eof;
                        ret = Some(Err(TokenizerError::UnfinishedEscapeSequence(
                            &self.str[self.start.offset+1..processing.offset],
                        )))
                    }
                },

                State::NumericStart => match c {
                    Some('0'..='9') => {}
                    Some('.') => self.state = State::NumericDecimal,
                    Some('e' | 'E') => {
                        self.state = State::NumericDecimalNumberE;
                    }
                    Some('_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Ok(Token::NumericLiteral {
                            str: self.str[self.start.offset..self.current.offset].into(),
                            hint: NumberType::Integer,
                        }));
                    }
                },
                State::NumericStartZero => match c {
                    Some('b') => {
                        self.state = State::NumericBinStart;
                    }
                    Some('x') => {
                        self.state = State::NumericHexStart;
                    }
                    Some('0'..='9') => {
                        self.state = State::NumericStart;
                    }
                    Some('.') => self.state = State::NumericDecimal,
                    Some('_') => {}
                    _ => {
                        consume = false;

                        ret = Some(Ok(Token::NumericLiteral {
                            str: self.str[self.start.offset..self.current.offset].into(),
                            hint: NumberType::Integer,
                        }));
                    }
                },
                State::NumericDecimal => match c {
                    Some('0'..='9') => {}
                    Some('e' | 'E') => {
                        self.state = State::NumericDecimalNumberE;
                    }
                    Some('_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Ok(Token::NumericLiteral {
                            str: self.str[self.start.offset..self.current.offset].into(),
                            hint: NumberType::Float,
                        }));
                    }
                },
                State::NumericDecimalNumberE => match c {
                    Some('0'..='9') => {
                        self.state = State::NumericDecimalNumberENumber;
                    }
                    Some('+' | '-') => {
                        self.state = State::NumericDecimalNumberEPM;
                    }
                    Some('_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Err(TokenizerError::EmptyExponent));
                    }
                },
                State::NumericDecimalNumberEPM => match c {
                    Some('0'..='9') => {
                        self.state = State::NumericDecimalNumberENumber;
                    }
                    Some('_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Err(TokenizerError::EmptyExponent));
                    }
                },
                State::NumericDecimalNumberENumber => match c {
                    Some('0'..='9' | '_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Ok(Token::NumericLiteral {
                            str: self.str[self.start.offset..self.current.offset].into(),
                            hint: NumberType::Float,
                        }));
                    }
                },
                State::NumericBinStart => match c {
                    Some('0'..='1') => {
                        self.state = State::NumericBin;
                    }
                    Some('_') => {}
                    Some(c @ '2'..='9') => {
                        err_ret_state = State::NumericBin;
                        ret_meta = Some(SpanD::start_end(self.current, processing));
                        update_start_on_error = false;
                        ret = Some(Err(TokenizerError::InvalidBase2Digit(c)))
                    }
                    _ => {
                        consume = false;
                        ret = Some(Err(TokenizerError::NoNumberAfterBasePrefix))
                    }
                },
                State::NumericBin => match c {
                    Some('0'..='1') => {}
                    Some('_') => {}
                    Some(c @ '2'..='9') => {
                        err_ret_state = State::NumericBin;
                        ret_meta = Some(SpanD::start_end(self.current, processing));
                        update_start_on_error = false;
                        ret = Some(Err(TokenizerError::InvalidBase2Digit(c)))
                    }
                    _ => {
                        consume = false;
                        ret = Some(Ok(Token::NumericLiteral {
                            str: self.str[self.start.offset..self.current.offset].into(),
                            hint: NumberType::Binary,
                        }));
                    }
                },
                State::NumericHexStart => match c {
                    Some('0'..='9' | 'a'..='f' | 'A'..='F') => {
                        self.state = State::NumericHex;
                    }
                    Some('_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Err(TokenizerError::NoNumberAfterBasePrefix))
                    }
                },
                State::NumericHex => match c {
                    Some('0'..='9' | 'a'..='f' | 'A'..='F') => {}
                    Some('_') => {}
                    _ => {
                        consume = false;
                        ret = Some(Ok(Token::NumericLiteral {
                            str: self.str[self.start.offset..self.current.offset].into(),
                            hint: NumberType::Hex,
                        }));
                    }
                },
                State::Eof => return None,
            }

            if consume {
                self.chars.next();
                self.current = processing;
            }

            if let Some(ret_some) = ret {
                match ret_some {
                    Ok(token) => {
                        let meta = ret_meta.unwrap_or(SpanD::start_end(self.start, self.current));
                        self.start = self.current;
                        self.state = ok_ret_state;
                        if matches!(
                            token,
                            Token::MultiLineComment(_) | Token::SingleLineComment(_)
                        ) && !self.include_comments
                        {
                            ret = None;
                            continue;
                        }
                        return Some(Ok(Span::new(token, meta)));
                    }
                    Err(err) => {
                        let meta = ret_meta.unwrap_or(SpanD::start_end(self.start, self.current));
                        if update_start_on_error {
                            self.start = self.current;
                        }
                        self.state = err_ret_state;
                        return Some(Err(Box::new(Span::new(err, meta))));
                    }
                }
            }
        }
    }
}

#[test]
pub fn test_tokenizer_full() {
    let data = r#"
    b"raw_string"
    b'raw_char'
    b'\xFF'
    b"\xFF"
    "\x7F"
    '\x7F'
    "\x8F"
    '\x9F'
    fadd    st1             ; this sets st0 := st0 + st1 
    fadd    st0,st1         ; so does this 

    fadd    st1,st0         ; this sets st1 := st1 + st0 
    fadd    to st1          ; so does this

    // this is also a comment
    /* so
    is 
    this */
    "multui
    line
    string"
    

    incbin  "file.dat"             ; include the whole file 
    incbin  "file.dat",1024        ; skip the first 1024 bytes 
    incbin  "file.dat",1024,512    ; skip the first 1024, and 
                                   ; actually include at most 512

    buffer:         resb    64              ; reserve 64 bytes 
    wordvar:        resw    1               ; reserve a word 
    realarray       resq    10              ; array of ten reals 
    ymmval:         resy    1               ; one YMM register

    db    0x55                ; just the byte 0x55 
    db    0x55,0x56,0x57      ; three bytes in succession 
    db    'a',0x55            ; character constants are OK 
    db    'hello',13,10,'$'   ; so are string constants 
    db    "String Literal\n\0"
    dw    0x1234              ; 0x34 0x12 
    dw    'a'                 ; 0x61 0x00 (it's just a number) 
    dw    'ab'                ; 0x61 0x62 (character constant) 
    dw    'abc'               ; 0x61 0x62 0x63 0x00 (string) 
    dd    0x12345678          ; 0x78 0x56 0x34 0x12 
    dd    1.234567e20         ; floating-point constant 
    dq    0x123456789abcdef0  ; eight byte constant 
    dq    1.234567e20         ; double-precision float 
    dt    1.234567e20         ; extended-precision float
    "#;

    let tokenizer = Tokenizer::new(data).include_comments();

    for token in tokenizer {
        match token {
            Ok(ok) => {
                let repr = &data[ok.span.offset as usize..(ok.span.offset + ok.span.len) as usize];
                println!("{:?} => {:?}", repr, ok)
            }
            Err(err) => {
                let repr =
                    &data[err.span.offset as usize..(err.span.offset + err.span.len) as usize];
                println!("Error {:?}: {:?}", repr, err)
            }
        }
    }
}