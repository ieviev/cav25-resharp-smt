#![allow(dead_code)]
/*!
RE# AST based on the regex_syntax crate.
*/

use regex_syntax::ast::{ClassBracketed, ClassPerl, ClassUnicode, Literal, Span};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Error {
    /// The kind of error.
    kind: ErrorKind,
    /// The original pattern that the parser generated the error from. Every
    /// span in an error is a valid range into this string.
    pattern: String,
    /// The span of this error.
    span: Span,
}

impl Error {
    /// Return the type of this error.
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }

    /// The original pattern string in which this error occurred.
    ///
    /// Every span reported by this error is reported in terms of this string.
    pub fn pattern(&self) -> &str {
        &self.pattern
    }

    /// Return the span at which this error occurred.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Return an auxiliary span. This span exists only for some errors that
    /// benefit from being able to point to two locations in the original
    /// regular expression. For example, "duplicate" errors will have the
    /// main error position set to the duplicate occurrence while its
    /// auxiliary span will be set to the initial occurrence.
    pub fn auxiliary_span(&self) -> Option<&Span> {
        use self::ErrorKind::*;
        match self.kind {
            FlagDuplicate { ref original } => Some(original),
            FlagRepeatedNegation { ref original, .. } => Some(original),
            GroupNameDuplicate { ref original, .. } => Some(original),
            _ => None,
        }
    }
}

/// The type of an error that occurred while building an AST.
///
/// This error type is marked as `non_exhaustive`. This means that adding a
/// new variant is not considered a breaking change.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    /// The capturing group limit was exceeded.
    ///
    /// Note that this represents a limit on the total number of capturing
    /// groups in a regex and not necessarily the number of nested capturing
    /// groups. That is, the nest limit can be low and it is still possible for
    /// this error to occur.
    CaptureLimitExceeded,
    /// An invalid escape sequence was found in a character class set.
    ClassEscapeInvalid,
    /// An invalid character class range was found. An invalid range is any
    /// range where the start is greater than the end.
    ClassRangeInvalid,
    /// An invalid range boundary was found in a character class. Range
    /// boundaries must be a single literal codepoint, but this error indicates
    /// that something else was found, such as a nested class.
    ClassRangeLiteral,
    /// An opening `[` was found with no corresponding closing `]`.
    ClassUnclosed,
    /// Note that this error variant is no longer used. Namely, a decimal
    /// number can only appear as a repetition quantifier. When the number
    /// in a repetition quantifier is empty, then it gets its own specialized
    /// error, `RepetitionCountDecimalEmpty`.
    DecimalEmpty,
    /// An invalid decimal number was given where one was expected.
    DecimalInvalid,
    /// A bracketed hex literal was empty.
    EscapeHexEmpty,
    /// A bracketed hex literal did not correspond to a Unicode scalar value.
    EscapeHexInvalid,
    /// An invalid hexadecimal digit was found.
    EscapeHexInvalidDigit,
    /// EOF was found before an escape sequence was completed.
    EscapeUnexpectedEof,
    /// An unrecognized escape sequence.
    EscapeUnrecognized,
    /// A dangling negation was used when setting flags, e.g., `i-`.
    FlagDanglingNegation,
    /// A flag was used twice, e.g., `i-i`.
    FlagDuplicate {
        /// The position of the original flag. The error position
        /// points to the duplicate flag.
        original: Span,
    },
    /// The negation operator was used twice, e.g., `-i-s`.
    FlagRepeatedNegation {
        /// The position of the original negation operator. The error position
        /// points to the duplicate negation operator.
        original: Span,
    },
    /// Expected a flag but got EOF, e.g., `(?`.
    FlagUnexpectedEof,
    /// Unrecognized flag, e.g., `a`.
    FlagUnrecognized,
    /// A duplicate capture name was found.
    GroupNameDuplicate {
        /// The position of the initial occurrence of the capture name. The
        /// error position itself points to the duplicate occurrence.
        original: Span,
    },
    /// A capture group name is empty, e.g., `(?P<>abc)`.
    GroupNameEmpty,
    /// An invalid character was seen for a capture group name. This includes
    /// errors where the first character is a digit (even though subsequent
    /// characters are allowed to be digits).
    GroupNameInvalid,
    /// A closing `>` could not be found for a capture group name.
    GroupNameUnexpectedEof,
    /// An unclosed group, e.g., `(ab`.
    ///
    /// The span of this error corresponds to the unclosed parenthesis.
    GroupUnclosed,
    /// An unopened group, e.g., `ab)`.
    GroupUnopened,
    /// The nest limit was exceeded. The limit stored here is the limit
    /// configured in the parser.
    NestLimitExceeded(u32),
    /// The range provided in a counted repetition operator is invalid. The
    /// range is invalid if the start is greater than the end.
    RepetitionCountInvalid,
    /// An opening `{` was not followed by a valid decimal value.
    /// For example, `x{}` or `x{]}` would fail.
    RepetitionCountDecimalEmpty,
    /// An opening `{` was found with no corresponding closing `}`.
    RepetitionCountUnclosed,
    /// A repetition operator was applied to a missing sub-expression. This
    /// occurs, for example, in the regex consisting of just a `*` or even
    /// `(?i)*`. It is, however, possible to create a repetition operating on
    /// an empty sub-expression. For example, `()*` is still considered valid.
    RepetitionMissing,
    /// The special word boundary syntax, `\b{something}`, was used, but
    /// either EOF without `}` was seen, or an invalid character in the
    /// braces was seen.
    SpecialWordBoundaryUnclosed,
    /// The special word boundary syntax, `\b{something}`, was used, but
    /// `something` was not recognized as a valid word boundary kind.
    SpecialWordBoundaryUnrecognized,
    /// The syntax `\b{` was observed, but afterwards the end of the pattern
    /// was observed without being able to tell whether it was meant to be a
    /// bounded repetition on the `\b` or the beginning of a special word
    /// boundary assertion.
    SpecialWordOrRepetitionUnexpectedEof,
    /// The Unicode class is not valid. This typically occurs when a `\p` is
    /// followed by something other than a `{`.
    UnicodeClassInvalid,
    /// When octal support is disabled, this error is produced when an octal
    /// escape is used. The octal escape is assumed to be an invocation of
    /// a backreference, which is the common case.
    UnsupportedBackreference,
    /// When syntax similar to PCRE's look-around is used, this error is
    /// returned. Some example syntaxes that are rejected include, but are
    /// not necessarily limited to, `(?=re)`, `(?!re)`, `(?<=re)` and
    /// `(?<!re)`. Note that all of these syntaxes are otherwise invalid; this
    /// error is used to improve the user experience.
    UnsupportedLookAround,
    ///
    UnsupportedResharpRegex,
    ComplementGroupExpected,
}

impl core::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use self::ErrorKind::*;
        match *self {
            CaptureLimitExceeded => write!(
                f,
                "exceeded the maximum number of \
                 capturing groups ({})",
                u32::MAX
            ),
            ClassEscapeInvalid => {
                write!(f, "invalid escape sequence found in character class")
            }
            ClassRangeInvalid => write!(
                f,
                "invalid character class range, \
                 the start must be <= the end"
            ),
            ClassRangeLiteral => {
                write!(f, "invalid range boundary, must be a literal")
            }
            ClassUnclosed => write!(f, "unclosed character class"),
            DecimalEmpty => write!(f, "decimal literal empty"),
            DecimalInvalid => write!(f, "decimal literal invalid"),
            EscapeHexEmpty => write!(f, "hexadecimal literal empty"),
            EscapeHexInvalid => {
                write!(f, "hexadecimal literal is not a Unicode scalar value")
            }
            EscapeHexInvalidDigit => write!(f, "invalid hexadecimal digit"),
            EscapeUnexpectedEof => write!(
                f,
                "incomplete escape sequence, \
                 reached end of pattern prematurely"
            ),
            EscapeUnrecognized => write!(f, "unrecognized escape sequence"),
            FlagDanglingNegation => {
                write!(f, "dangling flag negation operator")
            }
            FlagDuplicate { .. } => write!(f, "duplicate flag"),
            FlagRepeatedNegation { .. } => {
                write!(f, "flag negation operator repeated")
            }
            FlagUnexpectedEof => {
                write!(f, "expected flag but got end of regex")
            }
            FlagUnrecognized => write!(f, "unrecognized flag"),
            GroupNameDuplicate { .. } => {
                write!(f, "duplicate capture group name")
            }
            GroupNameEmpty => write!(f, "empty capture group name"),
            GroupNameInvalid => write!(f, "invalid capture group character"),
            GroupNameUnexpectedEof => write!(f, "unclosed capture group name"),
            GroupUnclosed => write!(f, "unclosed group"),
            GroupUnopened => write!(f, "unopened group"),
            NestLimitExceeded(limit) => write!(
                f,
                "exceed the maximum number of \
                 nested parentheses/brackets ({})",
                limit
            ),
            RepetitionCountInvalid => write!(
                f,
                "invalid repetition count range, \
                 the start must be <= the end"
            ),
            RepetitionCountDecimalEmpty => {
                write!(f, "repetition quantifier expects a valid decimal")
            }
            RepetitionCountUnclosed => {
                write!(f, "unclosed counted repetition")
            }
            RepetitionMissing => {
                write!(f, "repetition operator missing expression")
            }
            SpecialWordBoundaryUnclosed => {
                write!(
                    f,
                    "special word boundary assertion is either \
                     unclosed or contains an invalid character",
                )
            }
            SpecialWordBoundaryUnrecognized => {
                write!(
                    f,
                    "unrecognized special word boundary assertion, \
                     valid choices are: start, end, start-half \
                     or end-half",
                )
            }
            SpecialWordOrRepetitionUnexpectedEof => {
                write!(
                    f,
                    "found either the beginning of a special word \
                     boundary or a bounded repetition on a \\b with \
                     an opening brace, but no closing brace",
                )
            }
            UnicodeClassInvalid => {
                write!(f, "invalid Unicode character class")
            }
            UnsupportedBackreference => {
                write!(f, "backreferences are not supported")
            }
            UnsupportedLookAround => write!(
                f,
                "look-around, including look-ahead and look-behind, \
                 is not supported"
            ),
            UnsupportedResharpRegex => write!(f, "this pattern is not supported"),
            ComplementGroupExpected => write!(f, "expected ( after ~ for complement group"),
        }
    }
}

/// Span represents the position information of a single AST item.
///
/// All span positions are absolute byte offsets that can be used on the
/// original regular expression that was parsed.
// #[derive(Clone, Copy, Eq, PartialEq)]
// pub struct Span {
//     /// The start byte offset.
//     pub start: Position,
//     /// The end byte offset.
//     pub end: Position,
// }

// impl core::fmt::Debug for Span {
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         write!(f, "Span({:?}, {:?})", self.start, self.end)
//     }
// }

// impl Ord for Span {
//     fn cmp(&self, other: &Span) -> Ordering {
//         (&self.start, &self.end).cmp(&(&other.start, &other.end))
//     }
// }

// impl PartialOrd for Span {
//     fn partial_cmp(&self, other: &Span) -> Option<Ordering> {
//         Some(self.cmp(other))
//     }
// }

/// A single position in a regular expression.
///
/// A position encodes one half of a span, and include the byte offset, line
/// number and column number.
// #[derive(Clone, Copy, Eq, PartialEq)]
// pub struct Position {
//     /// The absolute offset of this position, starting at `0` from the
//     /// beginning of the regular expression pattern string.
//     pub offset: usize,
//     /// The line number, starting at `1`.
//     pub line: usize,
//     /// The approximate column number, starting at `1`.
//     pub column: usize,
// }

// impl core::fmt::Debug for Position {
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         write!(
//             f,
//             "Position(o: {:?}, l: {:?}, c: {:?})",
//             self.offset, self.line, self.column
//         )
//     }
// }

// impl Ord for Position {
//     fn cmp(&self, other: &Position) -> Ordering {
//         self.offset.cmp(&other.offset)
//     }
// }

// impl PartialOrd for Position {
//     fn partial_cmp(&self, other: &Position) -> Option<Ordering> {
//         Some(self.cmp(other))
//     }
// }

// impl Span {
//     /// Create a new span with the given positions.
//     pub fn new(start: Position, end: Position) -> Span {
//         Span { start, end }
//     }

//     /// Create a new span using the given position as the start and end.
//     pub fn splat(pos: Position) -> Span {
//         Span::new(pos, pos)
//     }

//     /// Create a new span by replacing the starting the position with the one
//     /// given.
//     pub fn with_start(self, pos: Position) -> Span {
//         Span { start: pos, ..self }
//     }

//     /// Create a new span by replacing the ending the position with the one
//     /// given.
//     pub fn with_end(self, pos: Position) -> Span {
//         Span { end: pos, ..self }
//     }

//     /// Returns true if and only if this span occurs on a single line.
//     pub fn is_one_line(&self) -> bool {
//         self.start.line == self.end.line
//     }

//     /// Returns true if and only if this span is empty. That is, it points to
//     /// a single position in the concrete syntax of a regular expression.
//     pub fn is_empty(&self) -> bool {
//         self.start.offset == self.end.offset
//     }
// }

// impl Position {
//     /// Create a new position with the given information.
//     ///
//     /// `offset` is the absolute offset of the position, starting at `0` from
//     /// the beginning of the regular expression pattern string.
//     ///
//     /// `line` is the line number, starting at `1`.
//     ///
//     /// `column` is the approximate column number, starting at `1`.
//     pub fn new(offset: usize, line: usize, column: usize) -> Position {
//         Position {
//             offset,
//             line,
//             column,
//         }
//     }
// }

/// An abstract syntax tree for a singular expression along with comments
/// found.
///
/// Comments are not stored in the tree itself to avoid complexity. Each
/// comment contains a span of precisely where it occurred in the original
/// regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WithComments {
    /// The actual ast.
    pub ast: Ast,
    /// All comments found in the original regular expression.
    pub comments: Vec<Comment>,
}

/// A comment from a regular expression with an associated span.
///
/// A regular expression can only contain comments when the `x` flag is
/// enabled.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Comment {
    /// The span of this comment, including the beginning `#` and ending `\n`.
    pub span: Span,
    /// The comment text, starting with the first character following the `#`
    /// and ending with the last character preceding the `\n`.
    pub comment: String,
}

/// An abstract syntax tree for a single regular expression.
///
/// An `Ast`'s `fmt::Display` implementation uses constant stack space and heap
/// space proportional to the size of the `Ast`.
///
/// This type defines its own destructor that uses constant stack space and
/// heap space proportional to the size of the `Ast`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ast {
    /// An empty regex that matches everything.
    Empty(Box<Span>),
    /// A set of flags, e.g., `(?is)`.
    Flags(Box<SetFlags>),
    /// A single character literal, which includes escape sequences.
    Literal(Box<Literal>),
    /// The "any character" class.
    Dot(Box<Span>),
    /// The "any character" class.
    Top(Box<Span>),
    /// A single zero-width assertion.
    Assertion(Box<Assertion>),
    /// A single Unicode character class, e.g., `\pL` or `\p{Greek}`.
    ClassUnicode(Box<ClassUnicode>),
    /// A single perl character class, e.g., `\d` or `\W`.
    ClassPerl(Box<ClassPerl>),
    /// A single bracketed character class set, which may contain zero or more
    /// character ranges and/or zero or more nested classes. e.g.,
    /// `[a-zA-Z\pL]`.
    ClassBracketed(Box<ClassBracketed>),
    /// A repetition operator applied to an arbitrary regular expression.
    Repetition(Box<Repetition>),
    /// A grouped regular expression.
    Group(Box<Group>),
    /// An alternation of regular expressions.
    Alternation(Box<Alternation>),
    /// A concatenation of regular expressions.
    Concat(Box<Concat>),
    // --------
    Intersection(Box<Intersection>),
    Complement(Box<Complement>),
    Lookaround(Box<Lookaround>),
    TaggedEps(Box<TaggedEps>),
}

impl Ast {
    /// Create an "empty" AST item.
    pub fn empty(span: Span) -> Ast {
        Ast::Empty(Box::new(span))
    }

    /// Create a "flags" AST item.
    pub fn flags(e: SetFlags) -> Ast {
        Ast::Flags(Box::new(e))
    }

    /// Create a "literal" AST item.
    pub fn literal(e: Literal) -> Ast {
        Ast::Literal(Box::new(e))
    }

    /// Create a "dot" AST item.
    pub fn dot(span: Span) -> Ast {
        Ast::Dot(Box::new(span))
    }

    pub fn top(span: Span) -> Ast {
        Ast::Top(Box::new(span))
    }

    /// Create a "assertion" AST item.
    pub fn assertion(e: Assertion) -> Ast {
        Ast::Assertion(Box::new(e))
    }

    /// Create a "Unicode class" AST item.
    pub fn class_unicode(e: ClassUnicode) -> Ast {
        Ast::ClassUnicode(Box::new(e))
    }

    /// Create a "Perl class" AST item.
    pub fn class_perl(e: ClassPerl) -> Ast {
        Ast::ClassPerl(Box::new(e))
    }

    /// Create a "bracketed class" AST item.
    pub fn class_bracketed(e: ClassBracketed) -> Ast {
        Ast::ClassBracketed(Box::new(e))
    }

    /// Create a "repetition" AST item.
    pub fn repetition(e: Repetition) -> Ast {
        Ast::Repetition(Box::new(e))
    }

    /// Create a "group" AST item.
    pub fn group(e: Group) -> Ast {
        match &e.kind {
            GroupKind::CaptureIndex(_) => Ast::Group(Box::new(e)),
            GroupKind::CaptureName {
                starts_with_p: _,
                name: _,
            } => Ast::Group(Box::new(e)),
            GroupKind::NonCapturing(_flags) => Ast::Group(Box::new(e)),
            GroupKind::Lookaround(kind) => {
                let look = Lookaround {
                    kind: kind.clone(),
                    span: e.span.clone(),
                    ast: e.ast,
                };
                let lookaround = Ast::lookaround(look);
                lookaround
            }
        }
    }

    /// Create a "alternation" AST item.
    pub fn alternation(e: Alternation) -> Ast {
        Ast::Alternation(Box::new(e))
    }

    /// Create a "concat" AST item.
    pub fn concat(e: Concat) -> Ast {
        Ast::Concat(Box::new(e))
    }

    /// Return the span of this abstract syntax tree.
    pub fn span(&self) -> &Span {
        match *self {
            Ast::Empty(ref span) => span,
            Ast::Flags(ref x) => &x.span,
            Ast::Literal(ref x) => &x.span,
            Ast::Dot(ref span) => span,
            Ast::Top(ref span) => span,
            Ast::Assertion(ref x) => &x.span,
            Ast::ClassUnicode(ref x) => &x.span,
            Ast::ClassPerl(ref x) => &x.span,
            Ast::ClassBracketed(ref x) => &x.span,
            Ast::Repetition(ref x) => &x.span,
            Ast::Group(ref x) => &x.span,
            Ast::Alternation(ref x) => &x.span,
            Ast::Concat(ref x) => &x.span,
            Ast::Intersection(ref x) => &x.span,
            Ast::Complement(ref x) => &x.span,
            Ast::Lookaround(ref x) => &x.span,
            Ast::TaggedEps(ref x) => &x.span,
        }
    }

    /// Return true if and only if this Ast is empty.
    pub fn is_empty(&self) -> bool {
        match *self {
            Ast::Empty(_) => true,
            _ => false,
        }
    }

    /// Returns true if and only if this AST has any (including possibly empty)
    /// subexpressions.
    fn has_subexprs(&self) -> bool {
        match *self {
            Ast::Empty(_)
            | Ast::Flags(_)
            | Ast::Literal(_)
            | Ast::Dot(_)
            | Ast::Top(_)
            | Ast::TaggedEps(_)
            | Ast::Assertion(_)
            | Ast::ClassUnicode(_)
            | Ast::ClassPerl(_) => false,
            Ast::ClassBracketed(_)
            | Ast::Repetition(_)
            | Ast::Group(_)
            | Ast::Alternation(_)
            | Ast::Intersection(_)
            | Ast::Lookaround(_)
            | Ast::Complement(_)
            | Ast::Concat(_) => true,
        }
    }
}

/// Print a display representation of this Ast.
///
/// This does not preserve any of the original whitespace formatting that may
/// have originally been present in the concrete syntax from which this Ast
/// was generated.
///
/// This implementation uses constant stack space and heap space proportional
/// to the size of the `Ast`.

/// An alternation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Alternation {
    /// The span of this alternation.
    pub span: Span,
    /// The alternate regular expressions.
    pub asts: Vec<Ast>,
}

impl Alternation {
    /// Return this alternation as an AST.
    ///
    /// If this alternation contains zero ASTs, then `Ast::empty` is returned.
    /// If this alternation contains exactly 1 AST, then the corresponding AST
    /// is returned. Otherwise, `Ast::alternation` is returned.
    pub fn into_ast(mut self) -> Ast {
        match self.asts.len() {
            0 => Ast::empty(self.span),
            1 => self.asts.pop().unwrap(),
            _ => Ast::alternation(self),
        }
    }
}

/// A concatenation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Concat {
    /// The span of this concatenation.
    pub span: Span,
    /// The concatenation regular expressions.
    pub asts: Vec<Ast>,
}

impl Concat {
    /// Return this concatenation as an AST.
    ///
    /// If this alternation contains zero ASTs, then `Ast::empty` is returned.
    /// If this alternation contains exactly 1 AST, then the corresponding AST
    /// is returned. Otherwise, `Ast::concat` is returned.
    pub fn into_ast(mut self) -> Ast {
        match self.asts.len() {
            0 => Ast::empty(self.span),
            1 => self.asts.pop().unwrap(),
            _ => Ast::concat(self),
        }
    }
}

/// A single zero-width assertion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Assertion {
    /// The span of this assertion.
    pub span: Span,
    /// The assertion kind, e.g., `\b` or `^`.
    pub kind: AssertionKind,
}

/// An assertion kind.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssertionKind {
    /// `^`
    StartLine,
    /// `$`
    EndLine,
    /// `\A`
    StartText,
    /// `\z`
    EndText,
    /// `\b`
    WordBoundary,
    /// `\B`
    NotWordBoundary,
    /// `\b{start}`
    WordBoundaryStart,
    /// `\b{end}`
    WordBoundaryEnd,
    /// `\<` (alias for `\b{start}`)
    WordBoundaryStartAngle,
    /// `\>` (alias for `\b{end}`)
    WordBoundaryEndAngle,
    /// `\b{start-half}`
    WordBoundaryStartHalf,
    /// `\b{end-half}`
    WordBoundaryEndHalf,
}

/// A repetition operation applied to a regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Repetition {
    /// The span of this operation.
    pub span: Span,
    /// The actual operation.
    pub op: RepetitionOp,
    /// Whether this operation was applied greedily or not.
    pub greedy: bool,
    /// The regular expression under repetition.
    pub ast: Box<Ast>,
}

/// The repetition operator itself.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepetitionOp {
    /// The span of this operator. This includes things like `+`, `*?` and
    /// `{m,n}`.
    pub span: Span,
    /// The type of operation.
    pub kind: RepetitionKind,
}

/// The kind of a repetition operator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepetitionKind {
    /// `?`
    ZeroOrOne,
    /// `*`
    ZeroOrMore,
    /// `+`
    OneOrMore,
    /// `{m,n}`
    Range(RepetitionRange),
}

/// A range repetition operator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepetitionRange {
    /// `{m}`
    Exactly(u32),
    /// `{m,}`
    AtLeast(u32),
    /// `{m,n}`
    Bounded(u32, u32),
}

impl RepetitionRange {
    /// Returns true if and only if this repetition range is valid.
    ///
    /// The only case where a repetition range is invalid is if it is bounded
    /// and its start is greater than its end.
    pub fn is_valid(&self) -> bool {
        match *self {
            RepetitionRange::Bounded(s, e) if s > e => false,
            _ => true,
        }
    }
}

/// A grouped regular expression.
///
/// This includes both capturing and non-capturing groups. This does **not**
/// include flag-only groups like `(?is)`, but does contain any group that
/// contains a sub-expression, e.g., `(a)`, `(?P<name>a)`, `(?:a)` and
/// `(?is:a)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Group {
    /// The span of this group.
    pub span: Span,
    /// The kind of this group.
    pub kind: GroupKind,
    /// The regular expression in this group.
    pub ast: Box<Ast>,
}

impl Group {
    /// If this group is non-capturing, then this returns the (possibly empty)
    /// set of flags. Otherwise, `None` is returned.
    pub fn flags(&self) -> Option<&Flags> {
        match self.kind {
            GroupKind::NonCapturing(ref flags) => Some(flags),
            _ => None,
        }
    }

    /// Returns true if and only if this group is capturing.
    pub fn is_capturing(&self) -> bool {
        match self.kind {
            GroupKind::CaptureIndex(_) | GroupKind::CaptureName { .. } => true,
            GroupKind::NonCapturing(_) => false,
            GroupKind::Lookaround(_) => false,
        }
    }

    /// Returns the capture index of this group, if this is a capturing group.
    ///
    /// This returns a capture index precisely when `is_capturing` is `true`.
    pub fn capture_index(&self) -> Option<u32> {
        match self.kind {
            GroupKind::CaptureIndex(i) => Some(i),
            GroupKind::CaptureName { ref name, .. } => Some(name.index),
            GroupKind::NonCapturing(_) => None,
            GroupKind::Lookaround(_) => None,
        }
    }
}

/// The kind of a group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GroupKind {
    /// `(a)`
    CaptureIndex(u32),
    /// `(?<name>a)` or `(?P<name>a)`
    CaptureName {
        /// True if the `?P<` syntax is used and false if the `?<` syntax is used.
        starts_with_p: bool,
        /// The capture name.
        name: CaptureName,
    },
    /// `(?:a)` and `(?i:a)`
    NonCapturing(Flags),
    Lookaround(LookaroundKind),
}

/// A capture name.
///
/// This corresponds to the name itself between the angle brackets in, e.g.,
/// `(?P<foo>expr)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaptureName {
    /// The span of this capture name.
    pub span: Span,
    /// The capture name.
    pub name: String,
    /// The capture index.
    pub index: u32,
}

// #[cfg(feature = "arbitrary")]
// impl arbitrary::Arbitrary<'_> for CaptureName {
//     fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<CaptureName> {
//         let len = u.arbitrary_len::<char>()?;
//         if len == 0 {
//             return Err(arbitrary::Error::NotEnoughData);
//         }
//         let mut name: String = String::new();
//         for _ in 0..len {
//             let ch: char = u.arbitrary()?;
//             let cp = u32::from(ch);
//             let ascii_letter_offset = u8::try_from(cp % 26).unwrap();
//             let ascii_letter = b'a' + ascii_letter_offset;
//             name.push(char::from(ascii_letter));
//         }
//         Ok(CaptureName {
//             span: u.arbitrary()?,
//             name,
//             index: u.arbitrary()?,
//         })
//     }

//     fn size_hint(depth: usize) -> (usize, Option<usize>) {
//         arbitrary::size_hint::and_all(&[
//             Span::size_hint(depth),
//             usize::size_hint(depth),
//             u32::size_hint(depth),
//         ])
//     }
// }

/// A group of flags that is not applied to a particular regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SetFlags {
    /// The span of these flags, including the grouping parentheses.
    pub span: Span,
    /// The actual sequence of flags.
    pub flags: Flags,
}

/// A group of flags.
///
/// This corresponds only to the sequence of flags themselves, e.g., `is-u`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Flags {
    /// The span of this group of flags.
    pub span: Span,
    /// A sequence of flag items. Each item is either a flag or a negation
    /// operator.
    pub items: Vec<FlagsItem>,
}

impl Flags {
    /// Add the given item to this sequence of flags.
    ///
    /// If the item was added successfully, then `None` is returned. If the
    /// given item is a duplicate, then `Some(i)` is returned, where
    /// `items[i].kind == item.kind`.
    pub fn add_item(&mut self, item: FlagsItem) -> Option<usize> {
        for (i, x) in self.items.iter().enumerate() {
            if x.kind == item.kind {
                return Some(i);
            }
        }
        self.items.push(item);
        None
    }

    /// Returns the state of the given flag in this set.
    ///
    /// If the given flag is in the set but is negated, then `Some(false)` is
    /// returned.
    ///
    /// If the given flag is in the set and is not negated, then `Some(true)`
    /// is returned.
    ///
    /// Otherwise, `None` is returned.
    pub fn flag_state(&self, flag: Flag) -> Option<bool> {
        let mut negated = false;
        for x in &self.items {
            match x.kind {
                FlagsItemKind::Negation => {
                    negated = true;
                }
                FlagsItemKind::Flag(ref xflag) if xflag == &flag => {
                    return Some(!negated);
                }
                _ => {}
            }
        }
        None
    }
}

/// A single item in a group of flags.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlagsItem {
    /// The span of this item.
    pub span: Span,
    /// The kind of this item.
    pub kind: FlagsItemKind,
}

/// The kind of an item in a group of flags.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlagsItemKind {
    /// A negation operator applied to all subsequent flags in the enclosing
    /// group.
    Negation,
    /// A single flag in a group.
    Flag(Flag),
}

impl FlagsItemKind {
    /// Returns true if and only if this item is a negation operator.
    pub fn is_negation(&self) -> bool {
        match *self {
            FlagsItemKind::Negation => true,
            _ => false,
        }
    }
}

/// A single flag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Flag {
    /// `i`
    CaseInsensitive,
    /// `m`
    MultiLine,
    /// `s`
    DotMatchesNewLine,
    /// `U`
    SwapGreed,
    /// `u`
    Unicode,
    /// `R`
    CRLF,
    /// `x`
    IgnoreWhitespace,
}

/// A custom `Drop` impl is used for `Ast` such that it uses constant stack
/// space but heap space proportional to the depth of the `Ast`.
// TODO: this overflows
// impl Drop for Ast {
//     fn drop(&mut self) {
//         use core::mem;

//         match *self {
//             Ast::Empty(_)
//             | Ast::Flags(_)
//             | Ast::Literal(_)
//             | Ast::Dot(_)
//             | Ast::Assertion(_)
//             | Ast::ClassUnicode(_)
//             | Ast::ClassPerl(_)
//             // Bracketed classes are recursive, they get their own Drop impl.
//             | Ast::ClassBracketed(_) => return,
//             Ast::Repetition(ref x) if !x.ast.has_subexprs() => return,
//             Ast::Group(ref x) if !x.ast.has_subexprs() => return,
//             Ast::Alternation(ref x) if x.asts.is_empty() => return,
//             Ast::Concat(ref x) if x.asts.is_empty() => return,
//             _ => {}
//         }

//         let empty_span = || Span::splat(Position::new(0, 0, 0));
//         let empty_ast = || Ast::empty(empty_span());
//         let mut stack = vec![mem::replace(self, empty_ast())];
//         while let Some(mut ast) = stack.pop() {
//             match ast {
//                 Ast::Empty(_)
//                 | Ast::Flags(_)
//                 | Ast::Literal(_)
//                 | Ast::Dot(_)
//                 | Ast::Assertion(_)
//                 | Ast::ClassUnicode(_)
//                 | Ast::ClassPerl(_)
//                 // Bracketed classes are recursive, so they get their own Drop
//                 // impl.
//                 | Ast::ClassBracketed(_) => {}
//                 Ast::Repetition(ref mut x) => {
//                     stack.push(mem::replace(&mut x.ast, empty_ast()));
//                 }
//                 Ast::Group(ref mut x) => {
//                     stack.push(mem::replace(&mut x.ast, empty_ast()));
//                 }
//                 Ast::Alternation(ref mut x) => {
//                     stack.extend(x.asts.drain(..));
//                 }
//                 Ast::Intersection(ref mut x) => {
//                     stack.extend(x.asts.drain(..));
//                 }
//                 Ast::Concat(ref mut x) => {
//                     stack.extend(x.asts.drain(..));
//                 }
//             }
//         }
//     }
// }

// /// A custom `Drop` impl is used for `ClassSet` such that it uses constant
// /// stack space but heap space proportional to the depth of the `ClassSet`.
// impl Drop for ClassSet {
//     fn drop(&mut self) {
//         use core::mem;

//         match *self {
//             ClassSet::Item(ref item) => match *item {
//                 ClassSetItem::Empty(_)
//                 | ClassSetItem::Literal(_)
//                 | ClassSetItem::Range(_)
//                 | ClassSetItem::Ascii(_)
//                 | ClassSetItem::Unicode(_)
//                 | ClassSetItem::Perl(_) => return,
//                 ClassSetItem::Bracketed(ref x) => {
//                     if x.kind.is_empty() {
//                         return;
//                     }
//                 }
//                 ClassSetItem::Union(ref x) => {
//                     if x.items.is_empty() {
//                         return;
//                     }
//                 }
//             },
//             ClassSet::BinaryOp(ref op) => {
//                 if op.lhs.is_empty() && op.rhs.is_empty() {
//                     return;
//                 }
//             }
//         }

//         let empty_span = || Span::splat(Position::new(0, 0, 0));
//         let empty_set = || ClassSet::Item(ClassSetItem::Empty(empty_span()));
//         let mut stack = vec![mem::replace(self, empty_set())];
//         while let Some(mut set) = stack.pop() {
//             match set {
//                 ClassSet::Item(ref mut item) => match *item {
//                     ClassSetItem::Empty(_)
//                     | ClassSetItem::Literal(_)
//                     | ClassSetItem::Range(_)
//                     | ClassSetItem::Ascii(_)
//                     | ClassSetItem::Unicode(_)
//                     | ClassSetItem::Perl(_) => {}
//                     ClassSetItem::Bracketed(ref mut x) => {
//                         stack.push(mem::replace(&mut x.kind, empty_set()));
//                     }
//                     ClassSetItem::Union(ref mut x) => {
//                         stack.extend(x.items.drain(..).map(ClassSet::Item));
//                     }
//                 },
//                 ClassSet::BinaryOp(ref mut op) => {
//                     stack.push(mem::replace(&mut op.lhs, empty_set()));
//                     stack.push(mem::replace(&mut op.rhs, empty_set()));
//                 }
//             }
//         }
//     }
// }

// START RE#

impl Ast {
    pub fn intersection(e: Intersection) -> Ast {
        Ast::Intersection(Box::new(e))
    }
    pub fn complement(e: Complement) -> Ast {
        Ast::Complement(Box::new(e))
    }
    pub fn lookaround(e: Lookaround) -> Ast {
        Ast::Lookaround(Box::new(e))
    }
    pub fn tagged_eps(e: TaggedEps) -> Ast {
        Ast::TaggedEps(Box::new(e))
    }
}

/// An alternation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Intersection {
    /// The span of this alternation.
    pub span: Span,
    /// The alternate regular expressions.
    pub asts: Vec<Ast>,
}

impl Intersection {
    pub fn into_ast(mut self) -> Ast {
        match self.asts.len() {
            0 => Ast::empty(self.span),
            1 => self.asts.pop().unwrap(),
            _ => Ast::intersection(self),
        }
    }
}

/// An alternation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Complement {
    /// The span of this alternation.
    pub span: Span,
    /// The regular expression in this group.
    pub ast: Box<Ast>,
}

impl Complement {
    pub fn into_ast(self) -> Ast {
        Ast::complement(self)
        // match self.asts.len() {
        //     0 => Ast::empty(self.span),
        //     1 => self.asts.pop().unwrap(),
        //     _ => Ast::intersection(self),
        // }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TaggedEps {
    /// The span of this operation.
    pub span: Span,
    /// The actual operation.
    pub num: u32,
}
impl TaggedEps {
    pub fn into_ast(self) -> Ast {
        Ast::tagged_eps(self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LookaroundKind {
    PositiveLookahead,
    NegativeLookahead,
    PositiveLookbehind,
    NegativeLookbehind,
}

/// An alternation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lookaround {
    pub kind: LookaroundKind,
    /// The span of this alternation.
    pub span: Span,
    /// The regular expression in this group.
    pub ast: Box<Ast>,
}

impl Lookaround {
    pub fn into_ast(self) -> Ast {
        Ast::lookaround(self)
    }
}
