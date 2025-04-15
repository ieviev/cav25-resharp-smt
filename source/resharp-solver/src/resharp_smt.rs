#![allow(dead_code)]
use core::panic;
use resharp_algebra::NodeId;
use resharp_parser::ResharpError;
use smt2parser::{
    concrete::{self},
    visitors::{
        CommandVisitor, ConstantVisitor, KeywordVisitor, QualIdentifierVisitor, SExprVisitor,
        Smt2Visitor, SortVisitor, SymbolVisitor, TermVisitor,
    },
    Binary, CommandStream, Decimal, Error, Hexadecimal, Numeral, Position,
};
use std::{
    collections::{BTreeMap, HashMap},
    vec,
};
pub struct SmtRegexBuilder {
    b: resharp_algebra::RegexBuilder,
}

impl SmtRegexBuilder {
    pub fn new() -> SmtRegexBuilder {
        SmtRegexBuilder {
            b: resharp_algebra::RegexBuilder::new(),
        }
    }

    // smt operations
    #[inline]
    pub fn byte_str_to_re(&mut self, s: &[u8]) -> NodeId {
        self.b.mk_bytestring(s)
    }
    #[inline]
    pub fn re_union(&mut self, left: NodeId, right: NodeId) -> NodeId {
        self.b.mk_union(left, right)
    }
    #[inline]
    pub fn re_inter(&mut self, left: NodeId, right: NodeId) -> NodeId {
        self.b.mk_inter(left, right)
    }
    #[inline]
    pub fn re_loop(&mut self, body: NodeId, low: u32, up: u32) -> NodeId {
        self.b.mk_loop(body, low, up)
    }
    #[inline]
    pub fn re_range(&mut self, low: u8, up: u8) -> NodeId {
        self.b.mk_range_u8(low, up)
    }
    #[inline]
    pub fn re_not(&mut self, body: NodeId) -> NodeId {
        self.b.mk_compl(body)
    }
    #[inline]
    pub fn re_top(&mut self) -> NodeId {
        NodeId::TOP
    }

    pub fn pp(&self, node_id: NodeId) -> String {
        self.b.pp(node_id)
    }

    #[inline]
    pub fn check_nonempty(&mut self, node_id: NodeId) -> bool {
        !self.b.is_empty_lang_cached(node_id)
    }

    #[inline]
    pub fn check_equiv(&mut self, node1: NodeId, node2: NodeId) -> bool {
        self.b.is_equiv(node1, node2)
    }

    pub fn transition(
        &mut self,
        state: NodeId,
        byte: u8,
        null_mask: resharp_algebra::Nullability,
    ) -> NodeId {
        let set = self.b.solver().u8_to_set_id(byte);
        let der = self.b.der(state, null_mask);
        let mut tregex = self.b.get_tregex(der);
        loop {
            match *tregex {
                resharp_algebra::TRegex::Leaf(node_id) => return node_id,
                resharp_algebra::TRegex::ITE(cond, _then, _else) => {
                    if self.b.solver().is_sat_id(set, cond) {
                        tregex = self.b.get_tregex(_then);
                    } else {
                        tregex = self.b.get_tregex(_else);
                    }
                }
            }
        }
    }

    pub fn is_match_smt(&mut self, start: NodeId, s: &[u8]) -> bool {
        use resharp_algebra::Nullability;
        if s.len() == 0 {
            return self.b.is_nullable_emptystring(start) != Nullability::NEVER;
        }
        let mut state = self.transition(start, s[0], Nullability::BEGIN);
        for i in 1..s.len() {
            state = self.transition(state, s[i], Nullability::CENTER);
        }
        return self.b.is_nullable(state, Nullability::END);
    }

    pub fn compile(&mut self, s: &str) -> std::result::Result<NodeId, ResharpError> {
        let parse_result = resharp_parser::parse_ast(&mut self.b, s);
        match parse_result {
            Ok(node_id) => return Ok(node_id),
            Err(e) => return Err(e),
        }
    }
}

pub struct Smt2Resharp {
    pub c: SmtRegexBuilder,
    pub declared_symbols: BTreeMap<String, Box<CommonSortKind>>,
    pub assertions: Vec<TermKind>,
    pub solved_assertions: HashMap<String, NodeId>,
    pub output: Vec<String>,
}

impl Smt2Resharp {
    pub fn new(_symbols: Vec<String>) -> Self {
        let state = Smt2Resharp {
            declared_symbols: BTreeMap::new(),
            c: SmtRegexBuilder::new(),
            assertions: Vec::new(),
            solved_assertions: HashMap::new(),
            output: Vec::new(),
        };

        state
    }
}

// extractors
impl Smt2Resharp {
    /// for debugging
    fn print_common_sort_kind(&self, idt: &str, csk: &CommonSortKind) -> String {
        match csk {
            CommonSortKind::String => {
                format!("{}: String", idt)
            }
            CommonSortKind::RegLan => {
                format!("{}: RegLan", idt)
            }
            CommonSortKind::Other => {
                format!("{}: Other", idt)
            }
            CommonSortKind::Term(term) => {
                let term_str = match &term {
                    TermKind::RegexNode(node_id) => {
                        format!("RegLan = {}", self.c.pp(*node_id))
                    }
                    TermKind::Constant(constant_kind) => format!("{:?}", constant_kind),
                    TermKind::Identifier(_) => format!("{:?}", term),
                    TermKind::StrInRe(_, _node_id) => format!("{:?}", term),
                    TermKind::StrLen(_) => format!("{:?}", term),
                    TermKind::Unknown => format!("{:?}", term),
                    TermKind::Equal(_) => todo!(),
                    _ => todo!(),
                };
                format!("{}: {}", idt, term_str)
            }
        }
    }

    fn debug_assertions(&mut self) {
        let mut symbol_assertions: HashMap<String, NodeId> = HashMap::new();
        let mut concrete_assertions: HashMap<&String, (Vec<u8>, NodeId)> = HashMap::new();
        for term in &self.assertions {
            match &term {
                TermKind::Constant(c) => match c {
                    ConstantKind::Boolean(b) => {
                        if !b {
                            println!("assertion: {:?}", term);
                            self.output.push("unsat".to_string());
                        }
                    }
                    _ => {
                        panic!("expected boolean constant");
                    }
                },
                TermKind::StrInRe(var, node_id) => {
                    let kind = self.declared_symbols.get(var).unwrap();
                    match kind.as_ref() {
                        CommonSortKind::String => {
                            let existing = symbol_assertions
                                .get(var)
                                .unwrap_or_else(|| &NodeId::TOPSTAR);
                            let updated = self.c.re_inter(*existing, *node_id);
                            symbol_assertions.insert(var.clone(), updated);
                        }
                        CommonSortKind::Term(witness) => {
                            let witness_str = self.term_get_byte_string(witness).unwrap();
                            concrete_assertions.insert(var, (witness_str, *node_id));
                        }
                        _ => {
                            panic!("expected concrete kind1");
                        }
                    }
                }
                _ => {
                    panic!("unknown assertion kind");
                }
            }
        }

        for assertion in &symbol_assertions {
            let (_var, node_id) = assertion;
            let result = self.c.check_nonempty(*node_id);
            println!("symbolic: {}: {} in {}", result, _var, self.c.pp(*node_id));
        }
        for assertion in concrete_assertions {
            let (_var, (str, node_id)) = assertion;
            let match_result = self.c.is_match_smt(node_id, str.as_slice());
            let result = match_result;
            let s = format!("concrete: {}: in {}: {}", result, _var, self.c.pp(node_id));
            println!("{}", s);
            let lossy = String::from_utf8_lossy(str.as_slice());
            println!("str: {:?}", lossy);
        }
    }

    fn throw_error(&self, msg: String) -> Error {
        Error::ParsingError(Position::default(), msg)
    }

    fn term_get_node_id(&self, t: &TermKind) -> Result<NodeId, Error> {
        match &t {
            TermKind::RegexNode(node_id) => Ok(*node_id),
            TermKind::Identifier(identifier) => {
                let err = || {
                    Error::ParsingError(
                        Position::default(),
                        format!("not found ({}: RegLan)", identifier),
                    )
                };

                self.declared_symbols
                    .get(identifier)
                    .map(|t| match t.as_ref() {
                        CommonSortKind::Term(term) => match term {
                            TermKind::RegexNode(node_id) => Ok(*node_id),
                            _ => Err(err()),
                        },
                        CommonSortKind::RegLan => {
                            // Ok(NodeId::TOPSTAR)
                            // Err(self.throw_error(format!(
                            //     "unbound regex {:?} not supported,\neither reorder assertions such {:?} is defined or use re.all if all strings was intended",
                            //     identifier, identifier
                            // )))
                            panic!(
                                "unassigned regex {:?} not supported, either:\n- reorder assertions such {:?} has a concrete RegLan before usage\n- or assign re.all if all strings was intended",
                                identifier, identifier
                            );
                        }
                        _ => Err(err()),
                    })
                    .unwrap_or_else(|| match identifier.as_str() {
                        "re.none" => Ok(NodeId::BOT),
                        "re.all" => Ok(NodeId::TOPSTAR),
                        "re.allchar" => Ok(NodeId::TOP),
                        _ => Err(err()),
                    })
            }
            _ => panic!("expected regex node: {:?}", t),
        }
    }

    fn term_get_ident(&self, t: &TermKind) -> String {
        match &t {
            TermKind::Identifier(ident) => ident.clone(),
            _ => panic!("expected identifier: {:?}", t),
        }
    }

    fn term_expand_ident<'b>(&self, t: TermKind) -> TermKind {
        match &t {
            TermKind::Identifier(ident) => match ident.as_str() {
                "re.none" => TermKind::RegexNode(NodeId::BOT),
                _ => match self.declared_symbols.get(ident) {
                    Some(decl) => match decl.as_ref() {
                        CommonSortKind::Term(term) => term.clone(),
                        CommonSortKind::RegLan => t,
                        CommonSortKind::String => t,
                        _ => panic!("expected concrete kind1: {:?}", decl),
                    },
                    None => panic!("expected: concrete kind: {:?}", ident),
                },
            },
            _ => t,
        }
    }

    fn term_get_char_range(&self, t: &TermKind) -> u32 {
        match &t {
            TermKind::Identifier(ident) => match self.declared_symbols.get(ident) {
                Some(decl) => match decl.as_ref() {
                    CommonSortKind::Term(ck) => return self.term_get_char_range(ck),
                    CommonSortKind::String => {
                        panic!("expected concrete kind");
                    }
                    _ => panic!("expected concrete kind"),
                },
                _ => panic!("expected concrete kind"),
            },
            TermKind::Constant(constant) => match constant {
                ConstantKind::ByteString(s) => {
                    debug_assert!(s.len() == 1, "{:?}", s);
                    s[0] as u32
                }
                ConstantKind::Numeral(s) => *s as u32,
                ConstantKind::String(s) => {
                    let bytes = s.as_bytes();
                    if bytes.len() == 1 {
                        return *bytes.iter().next().unwrap() as u32;
                    } else {
                        s.chars().next().unwrap() as u32
                    }
                }
                _ => panic!("expected string constant: {:?}", constant),
            },
            _ => panic!("expected constant string"),
        }
    }

    fn term_is_unbound_identifier(&self, t: &TermKind) -> bool {
        match &t {
            TermKind::Identifier(ident) => match self.declared_symbols.get(ident) {
                Some(decl) => match decl.as_ref() {
                    CommonSortKind::Term(_ck) => return false,
                    CommonSortKind::String => return true,
                    _ => panic!("expected identifier kind, got: {:?}", decl),
                },
                None => return true,
            },
            _ => false,
        }
    }
    fn term_get_integer(&self, t: &TermKind) -> Result<u32, Error> {
        match &t {
            TermKind::Constant(ck) => match ck {
                ConstantKind::Numeral(n) => Ok(*n),
                _ => Err(self.throw_error(format!("expected numeral, got: {:?}", ck))),
            },
            _ => Err(self.throw_error(format!("expected constant, got: {:?}", t))),
        }
    }

    fn term_get_str_len(&self, t: &TermKind) -> Result<String, Error> {
        match &t {
            TermKind::StrLen(s) => Ok(s.clone()),
            _ => panic!("expected string in re: {:?}", t),
        }
    }

    fn term_get_byte_string(&self, t: &TermKind) -> Result<Vec<u8>, Error> {
        match &t {
            TermKind::Identifier(ident) => match self.declared_symbols.get(ident) {
                Some(decl) => match decl.as_ref() {
                    CommonSortKind::Term(ck) => return self.term_get_byte_string(ck),
                    _ => Err(self.throw_error(format!("expected constant got: {:?}", decl))),
                },
                _ => panic!("expected concrete kind"),
            },
            TermKind::Constant(constant) => match constant {
                ConstantKind::String(s) => {
                    if s.is_ascii() {
                        return Ok(s.as_bytes().to_vec());
                    } else {
                        panic!("expected ascii string: {:?}", s);
                    }
                }
                ConstantKind::ByteString(s) => Ok(s.clone()),
                ConstantKind::Numeral(s) => Ok(vec![*s as u8]),
                _ => panic!("expected bstr constant: {:?}", constant),
            },
            _ => panic!("expected constant string"),
        }
    }

    fn term_get_const_string(&self, t: &TermKind) -> String {
        match &t {
            TermKind::Identifier(ident) => match self.declared_symbols.get(ident) {
                Some(decl) => match decl.as_ref() {
                    CommonSortKind::Term(ck) => return self.term_get_const_string(ck),
                    _ => panic!("expected concrete kind, got: {:?}", decl),
                },
                _ => panic!("expected concrete kind"),
            },
            TermKind::Constant(constant) => match constant {
                ConstantKind::String(s) => s.clone(),
                ConstantKind::Numeral(n) => {
                    if *n <= 255 {
                        return (*n as u8 as char).to_string();
                    }
                    println!("numeral: {:?}", n);
                    panic!("numeral");
                }
                ConstantKind::ByteString(s) => {
                    let utf8 = String::from_utf8_lossy(s);
                    utf8.to_string()
                }
                _ => panic!("expected string constant: {:?}", constant),
            },
            _ => panic!("expected constant string"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum TermKind {
    RegexNode(NodeId),
    Constant(ConstantKind),
    Identifier(String),
    StrInRe(String, NodeId),
    StrLen(String),
    StrToInt(String),
    Equal(Box<(TermKind, TermKind)>),
    #[default]
    Unknown,
}

struct Term {}

impl Term {
    fn identifier(name: String) -> TermKind {
        TermKind::Identifier(name)
    }

    fn constant(ck: ConstantKind) -> TermKind {
        TermKind::Constant(ck)
    }

    fn regex_node(node_id: NodeId) -> TermKind {
        TermKind::RegexNode(node_id)
    }

    fn str_in_re(identifier: String, node_id: NodeId) -> TermKind {
        TermKind::StrInRe(identifier, node_id)
    }

    fn str_to_int(identifier: String) -> TermKind {
        TermKind::StrToInt(identifier)
    }

    fn str_len(identifier: String) -> TermKind {
        TermKind::StrLen(identifier)
    }

    fn equal(term1: TermKind, term2: TermKind) -> TermKind {
        TermKind::Equal(Box::new((term1, term2)))
    }
}

impl ConstantVisitor for Smt2Resharp {
    type T = Constant;
    type E = Error;

    fn visit_numeral_constant(&mut self, _value: Numeral) -> Result<Self::T, Self::E> {
        let num_u32: Vec<_> = _value.iter_u32_digits().collect();
        let u32v = if num_u32.len() == 0 {
            0
        } else {
            debug_assert!(num_u32.len() == 1);
            num_u32[0]
        };
        Ok(ConstantKind::Numeral(u32v))
    }
    fn visit_decimal_constant(&mut self, _value: Decimal) -> Result<Self::T, Self::E> {
        Ok(ConstantKind::Decimal(_value))
    }
    fn visit_hexadecimal_constant(&mut self, _value: Hexadecimal) -> Result<Self::T, Self::E> {
        Ok(ConstantKind::Hexadecimal(_value))
    }
    fn visit_binary_constant(&mut self, _value: Binary) -> Result<Self::T, Self::E> {
        Ok(ConstantKind::Binary(_value))
    }
    fn visit_string_constant(&mut self, _value: String) -> Result<Self::T, Self::E> {
        let mut result: Vec<u8> = vec![];
        let mut escape_result: String = String::new();
        let mut esc1 = false;
        let mut esc2 = false;
        for b in _value.bytes() {
            match b {
                b'\\' => {
                    if esc1 {
                        result.push(b'\\');
                        esc1 = false;
                    } else {
                        esc1 = true;
                    }
                }
                b'u' => {
                    if esc1 {
                        esc1 = false;
                        esc2 = true;
                    } else {
                        result.push(b'u');
                    }
                }
                b'{' => {
                    if !esc2 {
                        result.push(b'{');
                    }
                }
                b'}' => {
                    if esc2 {
                        let num = u32::from_str_radix(&escape_result, 16).unwrap();
                        result.push(num as u8);
                        escape_result.clear();
                        esc2 = false;
                    } else {
                        result.push(b'}');
                    }
                }
                _ => {
                    if esc2 {
                        escape_result.push(b as char);
                    } else {
                        result.push(b);
                    }
                }
            }
        }
        // assert!(escape_result.len() == 0);
        // println!("other: string: {:?}, {:?}", result, _value);
        Ok(ConstantKind::ByteString(result))
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommonSortKind {
    String,
    RegLan,
    Other,
    Term(TermKind),
}

impl SymbolVisitor for Smt2Resharp {
    type T = Symbol;
    type E = Error;

    fn visit_fresh_symbol(
        &mut self,
        _value: String,
        _kind: smt2parser::visitors::SymbolKind,
    ) -> Result<Self::T, Self::E> {
        Ok(SymbolKind::Fresh(_value))
    }

    fn visit_bound_symbol(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(SymbolKind::Bound(value))
    }

    fn visit_any_symbol(&mut self, _value: String) -> Result<Self::T, Self::E> {
        Err(self.throw_error(format!("any symbol not implemented")))
    }

    fn unbind_symbol(&mut self, _symbol: &Self::T) {
        match _symbol {
            SymbolKind::Fresh(s) => {
                self.declared_symbols.remove(s);
            }
            SymbolKind::Bound(_) => {}
            SymbolKind::Any(_) => {}
        }
    }
}

impl KeywordVisitor for Smt2Resharp {
    type T = ();
    type E = Error;

    fn visit_keyword(&mut self, _value: String) -> Result<Self::T, Self::E> {
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstantKind {
    Boolean(bool),
    Numeral(u32),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(String),
    ByteString(Vec<u8>),
}

type Constant = ConstantKind;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Fresh(String),
    Bound(String),
    Any(String),
}

type Symbol = SymbolKind;
type Keyword = ();

#[derive(Debug)]
pub enum SortKind {
    CommonSort(CommonSortKind),
    Identifier(Identifier),
    Parameterized(Identifier, Vec<Sort>),
}

type Sort = SortKind;
type QualIdentifier = Identifier;
type SExpr = ();

pub enum CommandResultKind {
    Exit,
}
type CommandResult = Option<CommandResultKind>;

type Identifier = smt2parser::visitors::Identifier<Symbol>;
type AttributeValue = smt2parser::visitors::AttributeValue<Constant, Symbol, SExpr>;
type DatatypeDec = smt2parser::visitors::DatatypeDec<Symbol, Sort>;
type FunctionDec = smt2parser::visitors::FunctionDec<Symbol, Sort>;

impl SExprVisitor<Constant, Symbol, Keyword> for Smt2Resharp {
    type T = ();
    type E = Error;

    fn visit_constant_s_expr(&mut self, _value: Constant) -> Result<Self::T, Self::E> {
        Ok(())
    }

    fn visit_symbol_s_expr(&mut self, _value: Symbol) -> Result<Self::T, Self::E> {
        Ok(())
    }

    fn visit_keyword_s_expr(&mut self, _value: Keyword) -> Result<Self::T, Self::E> {
        Ok(())
    }

    fn visit_application_s_expr(&mut self, _values: Vec<Self::T>) -> Result<Self::T, Self::E> {
        Ok(())
    }
}

impl SortVisitor<Symbol> for Smt2Resharp {
    type T = Sort;
    type E = Error;

    fn visit_simple_sort(&mut self, _identifier: Identifier) -> Result<Self::T, Self::E> {
        match _identifier {
            concrete::Identifier::Simple { symbol } => {
                let kind = symbol;
                match kind {
                    SymbolKind::Bound(s) => match s.as_str() {
                        "String" => {
                            return Ok(SortKind::CommonSort(CommonSortKind::String));
                        }
                        "RegLan" => {
                            return Ok(SortKind::CommonSort(CommonSortKind::RegLan));
                        }
                        _ => {
                            unimplemented!("unknown sort: {:?}", s)
                        }
                    },
                    SymbolKind::Fresh(_) => todo!(),
                    SymbolKind::Any(_) => todo!(),
                }
            }
            concrete::Identifier::Indexed {
                symbol: _,
                indices: _,
            } => todo!(),
        }
    }

    fn visit_parameterized_sort(
        &mut self,
        _identifier: Identifier,
        _parameters: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        Err(self.throw_error(format!("unimplemented parameterized sort")))
    }
}

impl QualIdentifierVisitor<Identifier, Sort> for Smt2Resharp {
    type T = QualIdentifier;
    type E = Error;

    fn visit_simple_identifier(&mut self, _identifier: Identifier) -> Result<Self::T, Self::E> {
        Ok(_identifier)
    }

    fn visit_sorted_identifier(
        &mut self,
        _identifier: Identifier,
        _sort: Sort,
    ) -> Result<Self::T, Self::E> {
        Err(self.throw_error(format!("unimplemented sorted identifier")))
    }
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for Smt2Resharp {
    type T = TermKind;
    type E = Error;

    fn visit_constant(&mut self, _constant: Constant) -> Result<Self::T, Self::E> {
        Ok(Term::constant(_constant))
    }

    fn visit_qual_identifier(
        &mut self,
        _qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        match _qual_identifier {
            Identifier::Simple { symbol } => {
                let kind = symbol;
                match kind {
                    SymbolKind::Bound(name) => Ok(Term::identifier(name)),
                    SymbolKind::Fresh(_) => todo!(),
                    SymbolKind::Any(_) => todo!(),
                }
            }
            Identifier::Indexed { symbol: _, indices } => {
                let mut hex = vec![];
                assert!(indices.len() == 1);
                for h in indices {
                    match h {
                        smt2parser::visitors::Index::Numeral(_big_uint) => todo!(),
                        smt2parser::visitors::Index::Symbol(_) => todo!(),
                        smt2parser::visitors::Index::Hexadecimal(vec) => {
                            for i in vec {
                                hex.push(i);
                            }
                        }
                    }
                }
                if hex.len() == 1 {
                    let only1 = hex[0];
                    Ok(Term::constant(ConstantKind::Numeral(only1 as u32)))
                } else if hex.len() == 2 {
                    let d1 = hex[0];
                    let d2 = hex[1];
                    let num = (d1 as u32) << 4 | (d2 as u32);
                    Ok(Term::constant(ConstantKind::Numeral(num)))
                } else {
                    Err(self.throw_error(format!("unknown hex: {:?}", hex)))
                }
            }
        }
    }

    fn visit_application(
        &mut self,
        _qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        fn extract_index(t: &smt2parser::visitors::Index<SymbolKind>) -> u32 {
            match t {
                smt2parser::visitors::Index::Numeral(big_uint) => {
                    let num_u32: Vec<_> = big_uint.iter_u32_digits().collect();
                    if num_u32.len() == 0 {
                        return 0;
                    }
                    debug_assert!(num_u32.len() == 1);
                    let digit = num_u32[0];
                    return digit;
                }
                smt2parser::visitors::Index::Symbol(_) => todo!(""),
                smt2parser::visitors::Index::Hexadecimal(_vec) => todo!("PANIC"),
            }
        }

        match _qual_identifier {
            Identifier::Simple { symbol } => {
                match &symbol {
                    SymbolKind::Bound(s) => match s.as_str() {
                        "str.to_re" => {
                            debug_assert!(arguments.len() == 1);
                            let conststr = self.term_get_byte_string(&arguments[0])?;
                            return Ok(Term::regex_node(self.c.byte_str_to_re(&conststr)));
                        }

                        "re.parse" => {
                            debug_assert!(arguments.len() == 1);
                            let conststr = self.term_get_const_string(&arguments[0]);
                            let parsed = self.c.compile(&conststr).map_err(|_| {
                                Error::ParsingError(Position::default(), conststr.to_string())
                            })?;
                            return Ok(Term::regex_node(parsed));
                        }
                        "re.union" => {
                            let mut result = NodeId::BOT;
                            for arg in arguments.into_iter().rev() {
                                let node_id = self.term_get_node_id(&arg)?;
                                result = self.c.re_union(result, node_id);
                            }
                            return Ok(Term::regex_node(result));
                        }
                        "re.inter" => {
                            let mut result = NodeId::TOPSTAR;
                            for arg in arguments.into_iter().rev() {
                                let node_id = self.term_get_node_id(&arg)?;
                                result = self.c.re_inter(result, node_id);
                            }
                            return Ok(Term::regex_node(result));
                        }
                        "=" => {
                            debug_assert!(arguments.len() == 2, "expected 2 = arguments");
                            let left_expanded = self.term_expand_ident(arguments[0].clone());
                            let right_expanded = self.term_expand_ident(arguments[1].clone());

                            match (&left_expanded, &right_expanded) {
                                (TermKind::RegexNode(left_id), TermKind::RegexNode(right_id)) => {
                                    let result = self.c.check_equiv(*left_id, *right_id);
                                    return Ok(Term::constant(ConstantKind::Boolean(result)));
                                }
                                (
                                    TermKind::StrInRe(s, left_id),
                                    TermKind::StrInRe(s2, right_id),
                                ) => {
                                    if s == s2 {
                                        let result = self.c.check_equiv(*left_id, *right_id);
                                        return Ok(Term::constant(ConstantKind::Boolean(result)));
                                    } else {
                                        Err(self.throw_error(format!("regex equivalence on different strings not implemented")))
                                    }
                                }
                                (TermKind::Identifier(ident), other) => {
                                    // assigning the regex node to the identifier
                                    self.declared_symbols.insert(
                                        ident.clone(),
                                        Box::new(CommonSortKind::Term(other.clone())),
                                    );
                                    return Ok(Term::constant(ConstantKind::Boolean(true)));
                                }
                                (TermKind::Constant(_c), TermKind::StrLen(ident)) => {
                                    let num = self.term_get_integer(&left_expanded)?;
                                    let top = self.c.re_top();
                                    let len = self.c.re_loop(top, num, num);
                                    return Ok(Term::str_in_re(ident.to_string(), len));
                                }
                                (TermKind::Constant(_c1), TermKind::Constant(_c2)) => {
                                    // already bound to ident; dont need to do anything
                                    return Ok(Term::constant(ConstantKind::Boolean(true)));
                                }
                                (TermKind::StrToInt(_c1), TermKind::Constant(_c2)) => {
                                    let num = self.term_get_integer(&right_expanded)?;
                                    let num_str = num.to_string();
                                    self.declared_symbols.insert(
                                        _c1.clone(),
                                        Box::new(CommonSortKind::Term(TermKind::Constant(
                                            ConstantKind::String(num_str),
                                        ))),
                                    );
                                    return Ok(Term::constant(ConstantKind::Boolean(true)));
                                }
                                (TermKind::StrLen(ident), TermKind::Constant(_c2)) => {
                                    let num = self.term_get_integer(&right_expanded)?;
                                    let top = self.c.re_top();
                                    let len = self.c.re_loop(top, num, num);
                                    return Ok(Term::str_in_re(ident.to_string(), len));
                                }
                                _ => {
                                    panic!(
                                        "unimplemented = for terms: {:?} = {:?}",
                                        left_expanded, right_expanded
                                    );
                                }
                            }
                        }
                        "re.opt" => {
                            debug_assert!(arguments.len() == 1);
                            let left = self.term_get_node_id(&arguments[0])?;
                            return Ok(Term::regex_node(self.c.re_loop(left, 0, 1)));
                        }
                        "re.comp" => {
                            debug_assert!(arguments.len() == 1);
                            let left = self.term_get_node_id(&arguments[0])?;
                            return Ok(Term::regex_node(self.c.b.mk_compl(left)));
                        }
                        "re.+" => {
                            debug_assert!(arguments.len() == 1);
                            let left = self.term_get_node_id(&arguments[0])?;
                            return Ok(Term::regex_node(self.c.re_loop(left, 1, u32::MAX)));
                        }
                        "re.*" => {
                            debug_assert!(arguments.len() == 1);
                            let left = self.term_get_node_id(&arguments[0])?;
                            return Ok(Term::regex_node(self.c.re_loop(left, 0, u32::MAX)));
                        }
                        "re.all" => {
                            debug_assert!(arguments.len() == 0);
                            return Ok(Term::regex_node(NodeId::TOPSTAR));
                        }
                        "re.none" => {
                            debug_assert!(arguments.len() == 0);
                            return Ok(Term::regex_node(NodeId::BOT));
                        }
                        "re.++" => {
                            let new_concat =
                                arguments.iter().rev().try_fold(NodeId::EPS, |acc, tk| {
                                    let node = self.term_get_node_id(tk)?;
                                    // println!("concat: {:?}", self.c.pp(node));
                                    Ok(self.c.b.mk_concat(node, acc))
                                })?;
                            return Ok(Term::regex_node(new_concat));
                        }
                        "re.diff" => {
                            debug_assert!(arguments.len() == 2, "expected 2 arguments");
                            let left = self.term_get_node_id(&arguments[0])?;
                            let right = self.term_get_node_id(&arguments[1])?;
                            // a but not b
                            let notright = self.c.re_not(right);
                            return Ok(Term::regex_node(self.c.re_inter(left, notright)));
                        }
                        "not" => {
                            debug_assert!(arguments.len() == 1);
                            match self.term_expand_ident(arguments[0].clone()) {
                                TermKind::StrInRe(var, node_id) => {
                                    return Ok(Term::str_in_re(
                                        var.clone(),
                                        self.c.re_not(node_id),
                                    ));
                                }
                                TermKind::Constant(ConstantKind::Boolean(b)) => {
                                    return Ok(Term::constant(ConstantKind::Boolean(!b)));
                                }
                                _ => {
                                    Err(self
                                        .throw_error(format!("unimplemented not: {:?}", arguments)))
                                }
                            }
                        }
                        "and" => {
                            let mut combine2 = |a1: &TermKind, a2: &TermKind| match (
                                self.term_expand_ident(a1.clone()),
                                self.term_expand_ident(a2.clone()),
                            ) {
                                (
                                    TermKind::Constant(ConstantKind::Boolean(b1)),
                                    TermKind::Constant(ConstantKind::Boolean(b2)),
                                ) => {
                                    return Ok(Term::constant(ConstantKind::Boolean(b1 && b2)));
                                }
                                (
                                    TermKind::Constant(ConstantKind::Boolean(b1)),
                                    TermKind::StrInRe(_, _),
                                ) => {
                                    if !b1 {
                                        return Ok(Term::constant(ConstantKind::Boolean(false)));
                                    } else {
                                        return Ok(a2.clone());
                                    }
                                }
                                (
                                    TermKind::StrInRe(_, _),
                                    TermKind::Constant(ConstantKind::Boolean(b2)),
                                ) => {
                                    if !b2 {
                                        return Ok(Term::constant(ConstantKind::Boolean(false)));
                                    } else {
                                        return Ok(a1.clone());
                                    }
                                }
                                (TermKind::StrInRe(s1, r1), TermKind::StrInRe(s2, r2)) => {
                                    if s1 == s2 {
                                        return Ok(Term::str_in_re(
                                            s1.clone(),
                                            self.c.re_inter(r1, r2),
                                        ));
                                    } else {
                                        panic!("unimplemented and for 2 different strings:");
                                    }
                                }
                                _ => {
                                    panic!("unimplemented and: expected boolean constants");
                                }
                            };
                            // fold all arguments
                            arguments
                                .iter()
                                .try_fold(Term::constant(ConstantKind::Boolean(true)), |acc, x| {
                                    combine2(&acc, x)
                                })
                        }
                        "or" => {
                            let mut combine2 = |a1: &TermKind, a2: &TermKind| match (
                                self.term_expand_ident(a1.clone()),
                                self.term_expand_ident(a2.clone()),
                            ) {
                                (
                                    TermKind::Constant(ConstantKind::Boolean(b1)),
                                    TermKind::Constant(ConstantKind::Boolean(b2)),
                                ) => {
                                    return Ok(Term::constant(ConstantKind::Boolean(b1 || b2)));
                                }
                                (
                                    TermKind::Constant(ConstantKind::Boolean(b1)),
                                    TermKind::StrInRe(_, _),
                                ) => {
                                    if b1 {
                                        return Ok(Term::constant(ConstantKind::Boolean(true)));
                                    } else {
                                        return Ok(a2.clone());
                                    }
                                }
                                (
                                    TermKind::StrInRe(_, _),
                                    TermKind::Constant(ConstantKind::Boolean(b2)),
                                ) => {
                                    if b2 {
                                        return Ok(Term::constant(ConstantKind::Boolean(true)));
                                    } else {
                                        return Ok(a1.clone());
                                    }
                                }
                                (TermKind::StrInRe(s1, r1), TermKind::StrInRe(s2, r2)) => {
                                    let combo = self.c.re_union(r1, r2);
                                    if s1 == s2 {
                                        return Ok(Term::str_in_re(s1.clone(), combo));
                                    } else {
                                        panic!("unimplemented or for 2 different strings:");
                                    }
                                }
                                _ => {
                                    panic!("unimplemented or: expected boolean constants");
                                }
                            };
                            // fold all arguments
                            arguments
                                .iter()
                                .try_fold(Term::constant(ConstantKind::Boolean(false)), |acc, x| {
                                    combine2(&acc, x)
                                })
                        }
                        "str.in_re" => {
                            debug_assert!(arguments.len() == 2);
                            let identifier_name = self.term_get_ident(&arguments[0]);
                            let node_id = self.term_get_node_id(&arguments[1])?;
                            return Ok(Term::str_in_re(identifier_name, node_id));
                        }
                        "str.len" => {
                            debug_assert!(arguments.len() == 1);
                            let ident = self.term_get_ident(&arguments[0]);
                            let term = Term::str_len(ident.to_string());
                            return Ok(term);
                        }
                        "str.indexof" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.contains" => {
                            debug_assert!(arguments.len() == 2);
                            let ident = self.term_get_ident(&arguments[1]);
                            let conststr = self.term_get_byte_string(&arguments[0])?;
                            let body = self.c.byte_str_to_re(&conststr);
                            let contains_tail = self.c.b.mk_concat(body, NodeId::TOPSTAR);
                            let contains = self.c.b.mk_concat(NodeId::TOPSTAR, contains_tail);
                            return Ok(Term::str_in_re(ident, contains));
                        }
                        "str.suffixof" => {
                            debug_assert!(arguments.len() == 2);
                            let ident = self.term_get_ident(&arguments[1]);
                            let conststr = self.term_get_byte_string(&arguments[0])?;
                            let body = self.c.byte_str_to_re(&conststr);
                            let suffix = self.c.b.mk_concat(NodeId::TOPSTAR, body);
                            return Ok(Term::str_in_re(ident, suffix));
                        }
                        "str.prefixof" => {
                            debug_assert!(arguments.len() == 2);
                            let ident = self.term_get_ident(&arguments[1]);
                            let conststr = self.term_get_byte_string(&arguments[0])?;
                            let body = self.c.byte_str_to_re(&conststr);
                            let prefix = self.c.b.mk_concat(body, NodeId::TOPSTAR);
                            return Ok(Term::str_in_re(ident, prefix));
                        }
                        "str.replace" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.replace_all" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.replace_re_all" => {
                            Err(self.throw_error(format!("unimplemented {}", s)))
                        }
                        "str.replace_re" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.substr" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.at" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.<=" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.is_digit" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.to_code" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.from_code" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.from_int" => Err(self.throw_error(format!("unimplemented {}", s))),
                        "str.to_int" => {
                            debug_assert!(arguments.len() == 1);
                            let ident = self.term_get_ident(&arguments[0]);
                            return Ok(TermKind::StrToInt(ident));
                        }
                        "<=" => {
                            debug_assert!(arguments.len() == 2);
                            match self.term_get_integer(&arguments[0]) {
                                Ok(left) => match &arguments[1] {
                                    TermKind::StrLen(ident) => {
                                        let top = self.c.re_top();
                                        let len = self.c.re_loop(top, left, u32::MAX);
                                        return Ok(Term::str_in_re(ident.to_string(), len));
                                    }
                                    _ => {
                                        panic!("expected str.len");
                                    }
                                },
                                Err(_) => {
                                    let num = self.term_get_integer(&arguments[1])?;
                                    match &arguments[0] {
                                        TermKind::StrLen(ident) => {
                                            let top = self.c.re_top();
                                            let len = self.c.re_loop(top, 0, num);
                                            return Ok(Term::str_in_re(ident.to_string(), len));
                                        }
                                        _ => {
                                            panic!("expected str.len");
                                        }
                                    }
                                }
                            }
                        }
                        ">=" => {
                            debug_assert!(arguments.len() == 2);
                            match self.term_get_integer(&arguments[0]) {
                                Ok(left) => match &arguments[1] {
                                    TermKind::StrLen(ident) => {
                                        let top = self.c.re_top();
                                        let len = self.c.re_loop(top, 0, left);
                                        return Ok(Term::str_in_re(ident.to_string(), len));
                                    }
                                    _ => {
                                        panic!("expected str.len");
                                    }
                                },
                                Err(_) => {
                                    let num = self.term_get_integer(&arguments[1])?;
                                    match &arguments[0] {
                                        TermKind::StrLen(ident) => {
                                            let top = self.c.re_top();
                                            let len = self.c.re_loop(top, num, u32::MAX);
                                            return Ok(Term::str_in_re(ident.to_string(), len));
                                        }
                                        _ => {
                                            panic!("expected str.len");
                                        }
                                    }
                                }
                            }
                        }
                        ">" => {
                            debug_assert!(arguments.len() == 2);
                            let (lesser_than, num, str_ident) =
                                match self.term_get_integer(&arguments[0]) {
                                    Ok(left) => (true, left, self.term_get_str_len(&arguments[1])?),
                                    Err(_) => {
                                        let right = self.term_get_integer(&arguments[1])?;
                                        let left = self.term_get_str_len(&arguments[0])?;
                                        (false, right, left)
                                    }
                                };

                            let top = self.c.re_top();
                            if lesser_than {
                                let len = self.c.re_loop(top, 0, num - 1);
                                return Ok(Term::str_in_re(str_ident, len));
                            } else {
                                let len = self.c.re_loop(top, num + 1, u32::MAX);
                                return Ok(Term::str_in_re(str_ident, len));
                            }
                        }
                        "<" => {
                            debug_assert!(arguments.len() == 2);
                            let (lesser_than, num, str_ident) =
                                match self.term_get_integer(&arguments[1]) {
                                    Ok(left) => (true, left, self.term_get_str_len(&arguments[0])?),
                                    Err(_) => {
                                        let right = self.term_get_integer(&arguments[0])?;
                                        let left = self.term_get_str_len(&arguments[1])?;
                                        (false, right, left)
                                    }
                                };

                            let top = self.c.re_top();
                            if lesser_than {
                                let len = self.c.re_loop(top, 0, num - 1);
                                return Ok(Term::str_in_re(str_ident, len));
                            } else {
                                let len = self.c.re_loop(top, num + 1, u32::MAX);
                                return Ok(Term::str_in_re(str_ident, len));
                            }
                        }
                        "str.++" => {
                            debug_assert!(arguments.len() == 2);
                            const ERRMSG: &str = "symbolic str.++ unsupported, use regex concat";
                            let str1 = self
                                .term_get_byte_string(&arguments[0])
                                .map_err(|_e| self.throw_error(ERRMSG.to_string()))?;
                            let str2 = self
                                .term_get_byte_string(&arguments[1])
                                .map_err(|_e| self.throw_error(ERRMSG.to_string()))?;

                            let concated = [&str1[..], &str2[..]].concat();
                            return Ok(Term::constant(ConstantKind::ByteString(concated)));
                        }
                        "re.range" => {
                            debug_assert!(arguments.len() == 2);
                            let rangestart = self.term_get_char_range(&arguments[0]);
                            let rangeend = self.term_get_char_range(&arguments[1]);
                            if rangeend > 0xff {
                                return Err(self.throw_error(format!(
                                    "char range expected < 0xff, encode to utf8: {:?}",
                                    rangeend
                                )));
                            } else {
                                let reg = self.c.re_range(rangestart as u8, rangeend as u8);
                                return Ok(Term::regex_node(reg));
                            }
                        }
                        _ident => {
                            Err(self.throw_error(format!("unknown bound identifier: {:?}", _ident)))
                        }
                    },
                    _ => Err(self.throw_error(format!("unknown bound identifier: {:?}", symbol))),
                }
            }
            Identifier::Indexed { symbol, indices } => {
                match &symbol {
                    SymbolKind::Bound(s) => match s.as_str() {
                        "re.loop" => {
                            debug_assert!(arguments.len() == 1);
                            let indices_mapped: Vec<u32> =
                                indices.into_iter().map(|t| extract_index(&t)).collect();
                            let loop_body = self.term_get_node_id(&arguments[0]).unwrap();
                            let lower = indices_mapped[0];
                            let upper = indices_mapped[1];
                            return Ok(Term::regex_node(self.c.re_loop(loop_body, lower, upper)));
                        }
                        "re.^" => {
                            debug_assert!(arguments.len() == 1);
                            let num = extract_index(&indices[0]);
                            let loop_body = self.term_get_node_id(&arguments[0]).unwrap();
                            let new_node = self.c.re_loop(loop_body, num, num);
                            return Ok(Term::regex_node(new_node));
                        }
                        _ => {
                            unimplemented!("unknown indexed identifier: {:?}", symbol);
                        }
                    },
                    _ => {
                        unimplemented!("unknown indexed identifier: {:?}", symbol);
                    }
                };
            }
        }
    }

    fn visit_let(
        &mut self,
        _var_bindings: Vec<(Symbol, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(term)
    }

    fn visit_forall(
        &mut self,
        _vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(term)
    }

    fn visit_exists(
        &mut self,
        _vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(term)
    }

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        let _ = cases;
        Ok(term)
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        _attributes: Vec<(Keyword, AttributeValue)>,
    ) -> Result<Self::T, Self::E> {
        Ok(term)
    }

    fn bind_assign(&mut self, kind: &Symbol, term: &Self::T) -> () {
        match kind {
            SymbolKind::Bound(_s) => {
                unimplemented!("{:?}", kind)
            }
            SymbolKind::Fresh(s) => {
                self.declared_symbols
                    .insert(s.to_string(), Box::new(CommonSortKind::Term(term.clone())));
            }
            SymbolKind::Any(_) => {
                unimplemented!("{:?}", kind)
            }
        }
    }
}

impl CommandVisitor<TermKind, Symbol, Sort, Keyword, Constant, SExpr> for Smt2Resharp {
    type T = CommandResult;
    type E = Error;

    fn visit_assert(&mut self, term: TermKind) -> Result<Self::T, Self::E> {
        match &term {
            TermKind::StrInRe(_var, _node_idd) => {
                self.assertions.push(term);
            }
            TermKind::RegexNode(_node_id) => todo!(),
            TermKind::Constant(_constant_kind) => {
                self.assertions.push(term);
            }
            TermKind::Identifier(_) => {}

            TermKind::StrLen(_id) => {
                panic!("str.len not supported yet");
            }
            TermKind::Unknown => unimplemented!("{:?}", term),
            TermKind::Equal(_) => unimplemented!("{:?}", term),
            TermKind::StrToInt(_) => unimplemented!("{:?}", term),
        }
        Ok(None)
    }

    fn visit_check_sat(&mut self) -> Result<Self::T, Self::E> {
        let mut symbol_assertions: HashMap<String, NodeId> = HashMap::new();
        let mut concrete_assertions: HashMap<&String, (Vec<u8>, NodeId)> = HashMap::new();

        for term in &self.assertions {
            // println!("asserting: {term:?}");
            match &term {
                TermKind::Constant(c) => match c {
                    ConstantKind::Boolean(b) => {
                        if !b {
                            self.output.push("unsat".to_string());
                            return Ok(None);
                        }
                    }
                    _ => {
                        unimplemented!("expected boolean constant");
                    }
                },
                TermKind::StrInRe(var, node_id) => {
                    // println!("asserting: {:?} in {:?}", var, self.c.pp(*node_id));
                    let kind = self.declared_symbols.get(var).unwrap();
                    match kind.as_ref() {
                        CommonSortKind::String => {
                            let existing = symbol_assertions
                                .get(var)
                                .unwrap_or_else(|| &NodeId::TOPSTAR);
                            let updated = self.c.re_inter(*existing, *node_id);
                            // println!("updated: {:?}", self.c.pp(updated));
                            symbol_assertions.insert(var.clone(), updated);
                        }
                        CommonSortKind::Term(witness) => {
                            let witness_str = self.term_get_byte_string(witness)?;
                            concrete_assertions.insert(var, (witness_str, *node_id));
                        }
                        _ => {
                            unimplemented!("expected concrete kind");
                        }
                    }
                }
                _ => {
                    unimplemented!("unknown assertion kind");
                }
            }
        }
        let mut result = true;
        for assertion in &symbol_assertions {
            if !result {
                break;
            }
            result = self.c.check_nonempty(*assertion.1);
        }
        // is-match
        for assertion in concrete_assertions {
            if !result {
                break;
            }
            let (_var, (str, node_id)) = assertion;
            let match_result = self.c.is_match_smt(node_id, str.as_slice());
            result = match_result;
        }
        if result {
            self.output.push("sat".to_string());
        } else {
            self.output.push("unsat".to_string());
        }

        self.solved_assertions.clear();
        for assertion in symbol_assertions {
            let (var, node_id) = assertion;
            self.solved_assertions.insert(var, node_id);
        }
        Ok(None)
    }

    fn visit_check_sat_assuming(
        &mut self,
        _literals: Vec<(Symbol, bool)>,
    ) -> Result<Self::T, Self::E> {
        Ok(None)
    }

    fn visit_declare_const(&mut self, _symbol: Symbol, _sort: Sort) -> Result<Self::T, Self::E> {
        match _symbol {
            SymbolKind::Fresh(name) => match _sort {
                SortKind::CommonSort(common_sort_kind) => {
                    self.declared_symbols
                        .insert(name, Box::new(common_sort_kind));
                    Ok(None)
                }
                SortKind::Identifier(_identifier) => {
                    Err(self.throw_error(format!("unimplemented const")))
                }
                SortKind::Parameterized(_identifier, _vec) => {
                    Err(self.throw_error(format!("unimplemented const")))
                }
            },
            SymbolKind::Bound(_) => Err(self.throw_error(format!("unimplemented: {:?}", _symbol))),
            SymbolKind::Any(_) => Err(self.throw_error(format!("unimplemented const"))),
        }
    }

    fn visit_declare_datatype(
        &mut self,
        _symbol: Symbol,
        _datatype: DatatypeDec,
    ) -> Result<Self::T, Self::E> {
        Ok(None)
    }

    fn visit_declare_datatypes(
        &mut self,
        _datatypes: Vec<(Symbol, Numeral, DatatypeDec)>,
    ) -> Result<Self::T, Self::E> {
        Ok(None)
    }

    fn visit_declare_fun(
        &mut self,
        _symbol: Symbol,
        _parameters: Vec<Sort>,
        _sort: Sort,
    ) -> Result<Self::T, Self::E> {
        match _symbol {
            SymbolKind::Fresh(name) => {
                assert!(
                    _parameters.len() == 0,
                    "parameterized declare-fun not supported yet"
                );
                self.declared_symbols
                    .insert(name, Box::new(CommonSortKind::String));
            }
            _ => {
                unimplemented!("unknown symbol kind: {:?}", _symbol);
            }
        }
        Ok(None)
    }

    fn visit_declare_sort(&mut self, _symbol: Symbol, _arity: Numeral) -> Result<Self::T, Self::E> {
        Ok(None)
    }

    fn visit_define_fun(&mut self, _sig: FunctionDec, term: TermKind) -> Result<Self::T, Self::E> {
        match _sig {
            FunctionDec {
                name: SymbolKind::Fresh(fname),
                parameters,
                result: _,
            } => {
                assert!(
                    parameters.len() == 0,
                    "parameterized define-fun not supported yet"
                );
                self.declared_symbols
                    .insert(fname, Box::new(CommonSortKind::Term(term)));
            }
            _ => {
                unimplemented!("define-fun for bound {:?}", _sig);
            }
        }
        Ok(None)
    }

    fn visit_define_fun_rec(
        &mut self,
        _sig: FunctionDec,
        _term: TermKind,
    ) -> Result<Self::T, Self::E> {
        unimplemented!("define-fun-rec");
    }

    fn visit_define_funs_rec(
        &mut self,
        _funs: Vec<(FunctionDec, TermKind)>,
    ) -> Result<Self::T, Self::E> {
        unimplemented!("define-funs-rec");
    }

    fn visit_define_sort(
        &mut self,
        _symbol: Symbol,
        _parameters: Vec<Symbol>,
        _sort: Sort,
    ) -> Result<Self::T, Self::E> {
        unimplemented!("define-sort");
    }

    fn visit_echo(&mut self, _message: String) -> Result<Self::T, Self::E> {
        self.output.push(_message);
        Ok(None)
    }

    fn visit_exit(&mut self) -> Result<Self::T, Self::E> {
        Ok(Some(CommandResultKind::Exit))
    }

    fn visit_get_assertions(&mut self) -> Result<Self::T, Self::E> {
        self.output
            .push(";get-assertions is not implemented, printing solver state".to_string());
        self.debug_assertions();
        Ok(None)
    }

    fn visit_get_assignment(&mut self) -> Result<Self::T, Self::E> {
        unimplemented!("get-assignment");
    }

    fn visit_get_info(&mut self, _flag: Keyword) -> Result<Self::T, Self::E> {
        unimplemented!("get-info");
    }

    fn visit_get_model(&mut self) -> Result<Self::T, Self::E> {
        // self.output
        //     .push(";get-model is not implemented, printing values".to_string());
        self.solved_assertions.iter().for_each(|(var, node_id)| {
            let counterexample = self.c.b.is_empty_lang_w_counterexample(*node_id);
            let counterexample_str = match counterexample {
                Some(sat_node) => format!("\n\treachable sat: {}", self.c.b.pp(sat_node)),
                None => format!("\n\tempty language"),
            };

            self.output.push(format!(
                "str.in_re: {} {}, {}",
                var,
                self.c.pp(*node_id),
                counterexample_str
            ));
        });
        Ok(None)
    }

    fn visit_get_option(&mut self, _keyword: Keyword) -> Result<Self::T, Self::E> {
        unimplemented!("get_option");
    }

    fn visit_get_proof(&mut self) -> Result<Self::T, Self::E> {
        unimplemented!("get_proof");
    }

    fn visit_get_unsat_assumptions(&mut self) -> Result<Self::T, Self::E> {
        unimplemented!("unsat_assumptions");
    }

    fn visit_get_unsat_core(&mut self) -> Result<Self::T, Self::E> {
        unimplemented!("get_unsat_core");
    }

    fn visit_get_value(&mut self, _terms: Vec<TermKind>) -> Result<Self::T, Self::E> {
        unimplemented!("get_value");
    }

    fn visit_pop(&mut self, _level: Numeral) -> Result<Self::T, Self::E> {
        unimplemented!("pop");
    }

    fn visit_push(&mut self, _level: Numeral) -> Result<Self::T, Self::E> {
        unimplemented!("push");
    }

    fn visit_reset(&mut self) -> Result<Self::T, Self::E> {
        self.assertions.clear();
        self.declared_symbols.clear();
        self.solved_assertions.clear();
        self.c = SmtRegexBuilder::new();
        Ok(None)
    }

    fn visit_reset_assertions(&mut self) -> Result<Self::T, Self::E> {
        self.assertions.clear();
        Ok(None)
    }

    fn visit_set_info(
        &mut self,
        _keyword: Keyword,
        _value: AttributeValue,
    ) -> Result<Self::T, Self::E> {
        Ok(None)
    }

    fn visit_set_logic(&mut self, _symbol: Symbol) -> Result<Self::T, Self::E> {
        // only theory supported is regex
        Ok(None)
    }

    fn visit_set_option(
        &mut self,
        _keyword: Keyword,
        _value: AttributeValue,
    ) -> Result<Self::T, Self::E> {
        Ok(None)
    }
}

impl Smt2Visitor for Smt2Resharp {
    type Error = Error;
    type Constant = Constant;
    type QualIdentifier = QualIdentifier;
    type Keyword = ();
    type Sort = Sort;
    type SExpr = ();
    type Symbol = Symbol;
    type Term = TermKind;
    type Command = CommandResult;

    fn syntax_error(&mut self, position: Position, s: String) -> Self::Error {
        Error::SyntaxError(position, s)
    }

    fn parsing_error(&mut self, position: Position, s: String) -> Self::Error {
        Error::ParsingError(position, s)
    }
}

pub fn run_smt(input: &[u8]) -> Result<Vec<String>, Error> {
    let mut resharpsmt = Smt2Resharp::new(vec![]);
    let stream = CommandStream::new(input, concrete::SyntaxBuilder, None);

    let commands = stream.collect::<Result<Vec<_>, _>>()?;
    for command in commands {
        match command.accept(&mut resharpsmt) {
            Ok(None) => {}
            Ok(Some(CommandResultKind::Exit)) => {
                break;
            }
            Err(e) => {
                return Err(e);
            }
        }
    }
    Ok(resharpsmt.output)
}
