#![feature(portable_simd)]
use core::panic;
use solver::{Solver, TSetId};
use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::fmt::Write;
use std::hash::Hash;
use std::ops::{BitAnd, BitOr, Not};
use std::u32;
pub mod solver;

// certain nodes are hardcoded to ID numbers for optimization
mod id {
    pub const MISSING: u32 = 0;
    pub const EPS: u32 = 1;
    pub const BOT: u32 = 2;
    pub const TOP: u32 = 3;
    pub const TOPSTAR: u32 = 4;
    pub const BEGIN: u32 = 5;
    pub const END: u32 = 6;
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
pub struct MetadataId(u32);
impl MetadataId {
    pub const MISSING: MetadataId = MetadataId(id::MISSING);
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct NodeId(pub u32);
impl NodeId {
    pub const MISSING: NodeId = NodeId(id::MISSING);
    pub const EPS: NodeId = NodeId(id::EPS);
    pub const BOT: NodeId = NodeId(id::BOT);
    pub const TOP: NodeId = NodeId(id::TOP);
    pub const TOPSTAR: NodeId = NodeId(id::TOPSTAR);
    pub const BEGIN: NodeId = NodeId(id::BEGIN);
    pub const END: NodeId = NodeId(id::END);
}
impl Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let num = &self.0;
        f.write_str(format!("{num}").as_str())
    }
}
impl NodeId {
    fn missing_to_ts(&self) -> NodeId {
        if *self == NodeId::MISSING {
            NodeId::TOPSTAR
        } else {
            *self
        }
    }
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
pub struct TRegexId(u32);
impl TRegexId {
    pub const MISSING: TRegexId = TRegexId(id::MISSING);
    pub const EPS: TRegexId = TRegexId(id::EPS);
    pub const BOT: TRegexId = TRegexId(id::BOT);
    pub const TOP: TRegexId = TRegexId(id::TOP);
    pub const TOPSTAR: TRegexId = TRegexId(id::TOPSTAR);
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug)]
pub struct Nullability(u8);

impl BitAnd for Nullability {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Nullability(rhs.0 & self.0)
    }
}
impl BitOr for Nullability {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Nullability(rhs.0 | self.0)
    }
}
impl Not for Nullability {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        Nullability(!self.0)
    }
}
impl Nullability {
    pub const NEVER: Nullability = Nullability(0b000);
    pub const CENTER: Nullability = Nullability(0b001);
    pub const BEGIN: Nullability = Nullability(0b010);
    pub const END: Nullability = Nullability(0b100);
    pub const ALWAYS: Nullability = Nullability(0b111);
    pub const EMPTY_STRING: Nullability = Nullability(0b110);
}

#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug, PartialOrd, Ord)]
pub struct MetaFlags(u8);

impl BitAnd for MetaFlags {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        MetaFlags(rhs.0 & self.0)
    }
}
impl BitOr for MetaFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        MetaFlags(rhs.0 | self.0)
    }
}
impl Not for MetaFlags {
    type Output = Self;

    fn not(self) -> Self::Output {
        MetaFlags(!self.0)
    }
}

impl MetaFlags {
    pub const ZERO: MetaFlags = MetaFlags(0);
    pub const CENTER_NULLABLE: MetaFlags = MetaFlags(1);
    pub const BEGIN_NULLABLE: MetaFlags = MetaFlags(1 << 1);
    pub const END_NULLABLE: MetaFlags = MetaFlags(1 << 2);
    pub const ALL_NULLABILITIES: MetaFlags = MetaFlags(0b111);
    pub const CONTAINS_LOOKAROUND: MetaFlags = MetaFlags(1 << 3);
    pub const CONTAINS_LOOKBEHIND: MetaFlags = MetaFlags(1 << 4);
    pub const ALL_LOOKAROUNDS: MetaFlags = MetaFlags(0b11000);
    pub const INFINITE_LENGTH: MetaFlags = MetaFlags(1 << 5);
    pub const CONTAINS_COMPL: MetaFlags = MetaFlags(1 << 6);
    pub const CONTAINS_INTER: MetaFlags = MetaFlags(1 << 7);

    #[inline(always)]
    pub fn has_flag(self, other: MetaFlags) -> bool {
        self & other != MetaFlags::ZERO
    }

    pub fn pp(self) -> String {
        let mut result = String::new();
        if self.has_flag(MetaFlags::CONTAINS_LOOKBEHIND) {
            result.push_str("[lb]");
        }
        result
    }

    #[inline(always)]
    pub fn contains_lb(self) -> bool {
        self & MetaFlags::CONTAINS_LOOKBEHIND == MetaFlags::CONTAINS_LOOKBEHIND
    }

    #[inline(always)]
    pub fn any_nonbegin_null(self) -> bool {
        self & (MetaFlags::CENTER_NULLABLE | MetaFlags::END_NULLABLE) != MetaFlags::ZERO
    }

    #[inline(always)]
    pub fn is_infinite(self) -> bool {
        self & MetaFlags::INFINITE_LENGTH == MetaFlags::INFINITE_LENGTH
    }

    #[inline(always)]
    pub fn nullability(self) -> Nullability {
        Nullability(self.0 as u8 & 0b111)
    }
    #[inline(always)]
    pub fn nullability_flags(self) -> MetaFlags {
        self & MetaFlags(0b111)
    }
    #[inline(always)]
    pub fn contains_lookaround(self) -> MetaFlags {
        self & MetaFlags::CONTAINS_LOOKAROUND
    }

    #[inline(always)]
    pub fn contains_inter(self) -> bool {
        self & MetaFlags::CONTAINS_INTER != MetaFlags::ZERO
    }

    #[inline(always)]
    pub fn new(nullability: MetaFlags, contains_lookaround: MetaFlags) -> MetaFlags {
        nullability | contains_lookaround
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Kind {
    Eps = 1,
    Pred,
    Begin,
    End,
    Concat,
    Union,
    Loop,
    Compl,
    Lookbehind,
    Lookahead,
    Lookaround,
    Inter,
}

#[derive(Eq, Hash, PartialEq, Clone, PartialOrd, Ord)]
struct Metadata {
    /// set for pred, sum of all sets for others
    // psi: TSetId,
    flags: MetaFlags,
}

struct MetadataBuilder {
    solver: Solver,
    cache: BTreeMap<Metadata, MetadataId>,
    pub array: Vec<Metadata>,
}

impl MetadataBuilder {
    fn new() -> MetadataBuilder {
        Self {
            solver: Solver::new(),
            cache: BTreeMap::new(),
            array: Vec::new(),
        }
    }

    fn init(&mut self, inst: Metadata) -> MetadataId {
        let new_id = MetadataId(self.cache.len() as u32);
        self.cache.insert(inst.clone(), new_id);
        self.array.push(inst);
        new_id
    }

    fn get_meta_id(&mut self, inst: Metadata) -> MetadataId {
        match self.cache.get(&inst) {
            Some(&id) => id,
            None => self.init(inst),
        }
    }

    #[inline(always)]
    fn get_contains(&self, setflags: MetaFlags) -> MetaFlags {
        setflags & (MetaFlags::ALL_LOOKAROUNDS | MetaFlags::CONTAINS_INTER)
    }

    #[inline(always)]
    fn flags_pred(&self) -> MetaFlags {
        MetaFlags::ZERO
    }

    #[inline(always)]
    fn flags_eps(&self) -> MetaFlags {
        MetaFlags::ALL_NULLABILITIES
    }

    #[inline(always)]
    fn flags_look(&self, existing: MetaFlags) -> MetaFlags {
        existing | MetaFlags::CONTAINS_LOOKAROUND | MetaFlags::CONTAINS_INTER
    }

    fn flags_loop(&self, body: MetadataId, lower: u32, upper: u32) -> MetaFlags {
        let left = &self.array[body.0 as usize].flags;
        let nullabilities = if lower == 0 {
            MetaFlags::ALL_NULLABILITIES
        } else {
            left.nullability_flags()
        };
        let len = if upper == u32::MAX || left.is_infinite() {
            MetaFlags::INFINITE_LENGTH
        } else {
            MetaFlags::ZERO
        };
        let contains = *left & (MetaFlags::ALL_LOOKAROUNDS | MetaFlags::CONTAINS_INTER);
        let newflags = nullabilities | contains | len;
        newflags
    }

    fn flags_compl(&self, left_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let nullabilities = !left.nullability_flags() & MetaFlags::ALL_NULLABILITIES;
        let contains = self.get_contains(*left);
        let newflags = MetaFlags::new(nullabilities, contains)
            | MetaFlags::INFINITE_LENGTH
            | MetaFlags::CONTAINS_COMPL;
        newflags
    }

    fn flags_concat(&self, left_id: MetadataId, right_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let right = &self.array[right_id.0 as usize].flags;
        let nullabilities = left.nullability_flags() & right.nullability_flags();
        let contains = self.get_contains(*left | *right);
        let len = (*left | *right) & MetaFlags::INFINITE_LENGTH;
        let newflags = MetaFlags::new(nullabilities, contains) | len;
        newflags
    }

    fn flags_inter(&self, left_id: MetadataId, right_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let right = &self.array[right_id.0 as usize].flags;
        let nullabilities = left.nullability_flags() & right.nullability_flags();
        let contains = self.get_contains(*left | *right) | MetaFlags::CONTAINS_INTER;
        let len = (*left & *right) & MetaFlags::INFINITE_LENGTH;
        let newflags = MetaFlags::new(nullabilities, contains) | len;
        newflags
    }

    fn flags_union(&self, left_id: MetadataId, right_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let right = &self.array[right_id.0 as usize].flags;
        let nullabilities = left.nullability_flags() | right.nullability_flags();
        let contains = self.get_contains(*left | *right);
        let len = (*left | *right) & MetaFlags::INFINITE_LENGTH;
        let newflags = MetaFlags::new(nullabilities, contains) | len;
        newflags
    }

    fn merge_concat(&mut self, left_id: MetadataId, right_id: MetadataId) -> MetadataId {
        let new_meta = Metadata {
            flags: self.flags_concat(left_id, right_id),
        };
        let new_id = self.get_meta_id(new_meta);
        new_id
    }

    fn merge_union(&mut self, left_id: MetadataId, right_id: MetadataId) -> MetadataId {
        let new_meta = Metadata {
            flags: self.flags_union(left_id, right_id),
        };
        let new_id = self.get_meta_id(new_meta);
        new_id
    }

    fn merge_inter(&mut self, left_id: MetadataId, right_id: MetadataId) -> MetadataId {
        let new_meta = Metadata {
            flags: self.flags_inter(left_id, right_id),
        };
        let new_id = self.get_meta_id(new_meta);
        new_id
    }
}

#[derive(Eq, Hash, PartialEq, Clone)]
pub struct Node {
    pub kind: Kind,
    pub left: NodeId,
    pub right: NodeId,
    // extra field for loop upper bound or lookaround
    pub extra: u32,
    // extra field for metadata
    pub meta: MetadataId,
}

#[derive(Eq, Hash, PartialEq, Clone, Debug, Copy)]
pub enum TRegex<TSetId> {
    Leaf(NodeId),
    ITE(TSetId, TRegexId, TRegexId),
}

impl<T> TRegex<T>
where
    T: Eq,
    T: Hash,
    T: Clone,
{
}

#[derive(Eq, Hash, PartialEq, Clone, Copy)]
pub struct NodeFlags(u8);
impl NodeFlags {
    pub const ZERO: NodeFlags = NodeFlags(0);
    pub const CHECKED_EMPTY: NodeFlags = NodeFlags(1);
    pub const IS_EMPTY: NodeFlags = NodeFlags(1 << 1);
    fn is_checked(self) -> bool {
        self.0 >= NodeFlags::CHECKED_EMPTY.0
    }
    fn is_empty(self) -> bool {
        self.0 & NodeFlags::IS_EMPTY.0 == NodeFlags::IS_EMPTY.0
    }
}

pub struct RegexBuilder {
    mb: MetadataBuilder,
    // regex nodes
    cache: HashMap<Node, NodeId>,
    array: Vec<Node>,
    cache_empty: HashMap<NodeId, NodeFlags>,
    // symbolic regexes
    tr_cache: HashMap<TRegex<TSetId>, TRegexId>,
    tr_array: Vec<TRegex<TSetId>>,
    tr_der_center: Vec<TRegexId>,
    // number of keys created
    num_created: u32,
}

impl RegexBuilder {
    pub fn new() -> RegexBuilder {
        let mut inst = Self {
            mb: MetadataBuilder::new(),
            array: Vec::new(),
            cache: HashMap::new(),
            cache_empty: HashMap::new(),
            tr_array: Vec::new(),
            tr_cache: HashMap::new(),
            tr_der_center: Vec::new(),
            num_created: 0,
        };
        // hardcoded node ids
        // array[0] is for undefined nodes
        inst.array.push(Node {
            kind: Kind::Inter,
            left: NodeId::MISSING,
            right: NodeId::MISSING,
            extra: u32::MAX,
            meta: MetadataId::MISSING,
        });
        inst.mk_eps(0); // 1 - eps
        inst.mk_pred(TSetId::EMPTY); // 2 - bot
        inst.mk_pred(TSetId::FULL); // 3 - top
        inst.mk_loop(NodeId::TOP, 0, u32::MAX); // 4 - topstar
        inst.mk_unset(Kind::Begin); // 5 - begin
        inst.mk_unset(Kind::End); // 6 - end

        // hardcoded tregexes
        inst.tr_array.push(TRegex::Leaf(NodeId::MISSING)); // 0: missing
        inst.mk_leaf(NodeId::EPS); // 1 - eps
        inst.mk_leaf(NodeId::BOT); // 2 - bot
        inst.mk_leaf(NodeId::TOP); // 3 - top
        inst.mk_leaf(NodeId::TOPSTAR); // 4 - topstar
        inst
    }

    #[inline]
    pub fn solver(&mut self) -> &mut Solver {
        &mut self.mb.solver
    }

    /// ensures that left node id is always smaller or equal to right node id
    #[inline(always)]
    fn in_order(&self, n1: NodeId, n2: NodeId) -> (NodeId, NodeId) {
        if n1.0 < n2.0 {
            (n1, n2)
        } else {
            (n2, n1)
        }
    }

    fn tr_init(&mut self, inst: TRegex<TSetId>) -> TRegexId {
        let new_id = TRegexId(self.tr_cache.len() as u32 + 1);
        self.tr_cache.insert(inst.clone(), new_id);
        self.tr_array.push(inst);
        new_id
    }

    fn get_term_id(&mut self, inst: TRegex<TSetId>) -> TRegexId {
        match self.tr_cache.get(&inst) {
            Some(&id) => id,
            None => self.tr_init(inst),
        }
    }

    #[inline]
    fn get_cached_term_id(&mut self, inst: TRegex<TSetId>) -> Option<&TRegexId> {
        self.tr_cache.get(&inst)
    }

    #[inline]
    pub fn get_tregex(&self, inst: TRegexId) -> &TRegex<TSetId> {
        &self.tr_array[inst.0 as usize]
    }

    fn unsat_lengths(&self, minmax1: (u32, u32), minmax2: (u32, u32)) -> bool {
        let absmin = max(minmax1.0, minmax2.0);
        let absmax = min(minmax1.1, minmax2.1);
        if absmin > absmax {
            true
        } else {
            false
        }
    }

    fn unsat(&mut self, cond1: TSetId, cond2: TSetId) -> bool {
        let cd = self.mb.solver.and_id(cond1, cond2);
        self.mb.solver.is_empty_id(cd)
    }

    pub fn mk_leaf(&mut self, node_id: NodeId) -> TRegexId {
        let term = TRegex::<TSetId>::Leaf(node_id);
        self.get_term_id(term)
    }

    fn mk_ite(&mut self, cond: TSetId, _then: TRegexId, _else: TRegexId) -> TRegexId {
        if _then == _else {
            return _then;
        }
        let key = TRegex::ITE(cond, _then, _else);
        if let Some(cached) = self.get_cached_term_id(key) {
            return *cached;
        }
        if cond == TSetId::FULL {
            return _then;
        }
        if cond == TSetId::EMPTY {
            return _else;
        }
        let _clean_then = self.clean(cond, _then);
        let notcond = self.solver().not_id(cond);
        let _clean_else = self.clean(notcond, _else);

        if _clean_then == _clean_else {
            return _clean_then;
        }
        // attempt left side flattening: ITE(⊤,ITE(a,ε,⊥),⊥) -> ITE(a,ε,⊥)
        match *self.get_tregex(_clean_then) {
            TRegex::ITE(leftcond, _inner_then, leftg) if leftg == _clean_else => {
                let sand = self.solver().and_id(cond, leftcond);
                let new_then = _inner_then;
                return self.mk_ite(sand, new_then, _clean_else);
            }
            TRegex::ITE(leftcond, _inner_then, TRegexId::BOT) => {
                let _cond_then = leftcond;
                let c_it = _inner_then;
                let sand = self.solver().and_id(cond, _cond_then);
                return self.mk_ite(sand, c_it, _clean_else);
            }
            _ => {}
        }
        // attempt right side flattening:
        match *self.get_tregex(_clean_else) {
            // ITE(a,ε,ITE(b,ε,⊥)) -> ITE([ab],ε,⊥)
            TRegex::ITE(_c2, _t2, _e2) if _t2 == _clean_then => {
                let new_cond = self.solver().or_id(cond, _c2);
                return self.mk_ite(new_cond, _clean_then, _e2);
            }
            _ => {}
        }

        let cleaned_id = self.get_term_id(TRegex::ITE(cond, _clean_then, _clean_else));
        cleaned_id
    }

    fn clean(&mut self, beta: TSetId, tterm: TRegexId) -> TRegexId {
        match *self.get_tregex(tterm) {
            TRegex::Leaf(_) => return tterm,
            TRegex::ITE(alpha, _then_id, _else_id) => {
                let notalpha = self.mb.solver.not_id(alpha);
                if self.mb.solver.unsat_id(beta, alpha) {
                    let ec = self.mb.solver.and_id(beta, notalpha);
                    let new_else = self.clean(ec, _else_id);
                    return new_else;
                }
                if self.unsat(beta, notalpha) {
                    let tc = self.mb.solver.and_id(beta, alpha);
                    let new_then = self.clean(tc, _then_id);
                    return new_then;
                }
                let ei = _else_id;
                let tc = self.mb.solver.and_id(beta, alpha);
                let ec = self.mb.solver.and_id(beta, notalpha);
                let new_then = self.clean(tc, _then_id);
                let new_else = self.clean(ec, ei);
                return self.mk_ite(tc, new_then, new_else);
            }
        }
    }

    #[inline]
    fn mk_unary(
        &mut self,
        term: TRegexId,
        apply: &mut impl FnMut(&mut RegexBuilder, NodeId) -> NodeId,
    ) -> TRegexId {
        match self.tr_array[term.0 as usize] {
            TRegex::Leaf(node_id) => {
                let applied = apply(self, node_id);
                self.mk_leaf(applied)
            }
            TRegex::ITE(c1, _then, _else) => {
                let _then1 = self.mk_unary(_then, apply);
                let _else1 = self.mk_unary(_else, apply);
                self.mk_ite(c1, _then1, _else1)
            }
        }
    }

    #[inline]
    fn mk_binary(
        &mut self,
        left: TRegexId,
        right: TRegexId,
        apply: &mut impl FnMut(&mut RegexBuilder, NodeId, NodeId) -> NodeId,
    ) -> TRegexId {
        match self.tr_array[left.0 as usize] {
            TRegex::Leaf(left_node_id) => match self.tr_array[right.0 as usize] {
                TRegex::Leaf(right_node_id) => {
                    let applied = apply(self, left_node_id, right_node_id);
                    self.mk_leaf(applied)
                }
                TRegex::ITE(c2, _then, _else) => {
                    let then2 = self.mk_binary(left, _then, apply);
                    let else2 = self.mk_binary(left, _else, apply);
                    self.mk_ite(c2, then2, else2)
                }
            },
            TRegex::ITE(c1, _then1, _else1) => match self.tr_array[right.0 as usize] {
                TRegex::Leaf(_) => {
                    let then2 = self.mk_binary(_then1, right, apply);
                    let else2 = self.mk_binary(_else1, right, apply);
                    self.mk_ite(c1, then2, else2)
                }
                TRegex::ITE(c2, _then2, _else2) => {
                    if c1 == c2 {
                        let _then = self.mk_binary(_then1, _then2, apply);
                        let _else = self.mk_binary(_else1, _else2, apply);
                        return self.mk_ite(c1, _then, _else);
                    }
                    if c1.0 > c2.0 {
                        let _then = self.mk_binary(_then1, right, apply);
                        let _else = self.mk_binary(_else1, right, apply);
                        return self.mk_ite(c1, _then, _else);
                    } else {
                        let _then = self.mk_binary(left, _then2, apply);
                        let _else = self.mk_binary(left, _else2, apply);
                        return self.mk_ite(c2, _then, _else);
                    }
                }
            },
        }
    }

    fn tr_mk_compl(&mut self, tregex: TRegexId) -> TRegexId {
        self.mk_unary(tregex, &mut (|b, v| b.mk_compl(v)))
    }

    fn tr_mk_inter(&mut self, left: TRegexId, right: TRegexId) -> TRegexId {
        self.mk_binary(left, right, &mut (|b, left, right| b.mk_inter(left, right)))
    }

    fn tr_mk_union(&mut self, left: TRegexId, right: TRegexId) -> TRegexId {
        self.mk_binary(left, right, &mut (|b, left, right| b.mk_union(left, right)))
    }

    // effectively the same, but wrapping right is not needed
    // fn tr_mk_concat(&mut self, left: TRegexId, right: TRegexId) -> TRegexId {
    //     self.mk_binary(left, right, &mut (|b,left,right| b.mk_concat(left,right)))
    // }

    fn tr_mk_concat(&mut self, head: TRegexId, tail: NodeId) -> TRegexId {
        if head == TRegexId::EPS {
            return self.mk_leaf(tail);
        }
        if head == TRegexId::BOT {
            return TRegexId::BOT;
        }
        let result = match *self.get_tregex(head) {
            TRegex::Leaf(l) => {
                let tmp = self.mk_concat(l, tail);
                self.mk_leaf(tmp)
            }
            TRegex::ITE(cond, _then, _else) => {
                let left = self.tr_mk_concat(_then, tail);
                let right = self.tr_mk_concat(_else, tail);
                self.mk_ite(cond, left, right)
            }
        };
        result
    }

    fn tr_lookaround_wrap_2(&mut self, body: TRegexId, look_ahead: NodeId) -> TRegexId {
        match *self.get_tregex(body) {
            TRegex::Leaf(l) => {
                let conc = self.mk_lookaround(NodeId::MISSING, l, look_ahead);
                self.mk_leaf(conc)
            }
            TRegex::ITE(c1, _then, _else) => {
                let then_id = self.tr_lookaround_wrap_2(_then, look_ahead);
                let else_id = self.tr_lookaround_wrap_2(_else, look_ahead);
                self.mk_ite(c1, then_id, else_id)
            }
        }
    }

    fn tr_lookaround_wrap_1(
        &mut self,
        look_behind: TRegexId,
        body: NodeId,
        look_ahead: NodeId,
    ) -> TRegexId {
        match *self.get_tregex(look_behind) {
            TRegex::Leaf(l) => {
                let conc = self.mk_lookaround(l, body, look_ahead);
                self.mk_leaf(conc)
            }
            TRegex::ITE(c1, _then, _else) => {
                let then_id = self.tr_lookaround_wrap_1(_then, body, look_ahead);
                let else_id = self.tr_lookaround_wrap_1(_else, body, look_ahead);
                self.mk_ite(c1, then_id, else_id)
            }
        }
    }

    fn tr_mk_lookbehind(&mut self, term1: TRegexId) -> TRegexId {
        match *self.get_tregex(term1) {
            TRegex::Leaf(node_id) => {
                let temp = self.mk_lookbehind(node_id);
                self.mk_leaf(temp)
            }
            TRegex::ITE(c1, _then, _else) => {
                let _then1 = self.tr_mk_lookbehind(_then);
                let _else1 = self.tr_mk_lookbehind(_else);
                self.mk_ite(c1, _then1, _else1)
            }
        }
    }

    fn tr_mk_lookahead(&mut self, term1: TRegexId, rel: u32) -> TRegexId {
        match *self.get_tregex(term1) {
            TRegex::Leaf(node_id) => {
                let temp = self.mk_lookahead(node_id, rel);
                self.mk_leaf(temp)
            }
            TRegex::ITE(c1, _then, _else) => {
                let _then1 = self.tr_mk_lookahead(_then, rel);
                let _else1 = self.tr_mk_lookahead(_else, rel);
                self.mk_ite(c1, _then1, _else1)
            }
        }
    }

    pub fn meta_contains_inter(&self, node_id: NodeId) -> bool {
        self.get_meta_flags(node_id).0 & MetaFlags::CONTAINS_INTER.0 != 0
    }

    pub fn meta_is_infinite(&self, node_id: NodeId) -> bool {
        self.get_meta_flags(node_id).0 & MetaFlags::INFINITE_LENGTH.0 != 0
    }

    pub fn contains_look(&mut self, node_id: NodeId) -> bool {
        let f = self.get_meta_flags(node_id).0;
        f & MetaFlags::CONTAINS_LOOKAROUND.0 == MetaFlags::CONTAINS_LOOKAROUND.0
    }

    pub fn get_min_max_len(&self, node_id: NodeId) -> (u32, u32) {
        if self.meta_is_infinite(node_id) {
            let min_bound = self.get_min_length_only(node_id);
            return (min_bound, u32::MAX);
        } else {
            return self.get_min_max_len_both(node_id);
        }
    }

    fn get_min_length_only(&self, node_id: NodeId) -> u32 {
        match self.get_kind(node_id) {
            Kind::End | Kind::Begin | Kind::Eps => 0,
            Kind::Pred => 1,
            Kind::Concat => {
                let left_len = self.get_min_length_only(self.get_left(node_id));
                let right_len = self.get_min_length_only(self.get_right(node_id));
                left_len + right_len
            }
            Kind::Union => {
                let left_len = self.get_min_length_only(self.get_left(node_id));
                let right_len = self.get_min_length_only(self.get_right(node_id));
                left_len.min(right_len)
            }
            Kind::Inter => {
                let left_len = self.get_min_length_only(self.get_left(node_id));
                let right_len = self.get_min_length_only(self.get_right(node_id));
                // could be more, this is at least the length
                // if no overlap this is at least left + right
                left_len.max(right_len)
            }
            Kind::Loop => {
                let body = self.get_min_length_only(self.get_left(node_id));
                let lower = body * self.get_right(node_id).0;
                lower
            }
            Kind::Compl => {
                // inner not nullable - meaning min-length is 0
                if self.nullability(self.get_left(node_id)) == Nullability::NEVER {
                    0
                } else {
                    1 // overapproximation
                }
            }
            Kind::Lookbehind => {
                0 // overapproximation
            }
            Kind::Lookahead => {
                0 // overapproximation
            }
            Kind::Lookaround => self.get_min_length_only(NodeId(self.get_extra(node_id))),
        }
    }

    fn get_min_max_len_both(&self, node_id: NodeId) -> (u32, u32) {
        debug_assert!(
            !self.meta_is_infinite(node_id),
            "node is infinite, : {:?}",
            self.pp(node_id)
        );
        match self.get_kind(node_id) {
            Kind::Eps | Kind::Begin | Kind::End => (0, 0),
            Kind::Pred => (1, 1),
            Kind::Concat => {
                let left = self.get_min_max_len_both(self.get_left(node_id));
                let right = self.get_min_max_len_both(self.get_right(node_id));
                let new_bounds = (left.0 + right.0, left.1 + right.1);
                new_bounds
            }
            Kind::Union => {
                let left = self.get_min_max_len_both(self.get_left(node_id));
                let right = self.get_min_max_len_both(self.get_right(node_id));
                let new_bounds = (left.0.min(right.0), left.1.max(right.1));
                new_bounds
            }
            Kind::Inter => {
                let left = self.get_min_max_len(self.get_left(node_id));
                let right = self.get_min_max_len(self.get_right(node_id));
                let new_bounds = (left.0.max(right.0), left.1.min(right.1));
                new_bounds
            }
            Kind::Loop => {
                let body = self.get_min_max_len_both(self.get_left(node_id));
                (
                    body.0 * self.get_right(node_id).0,
                    body.1 * self.get_extra(node_id),
                )
            }
            Kind::Compl => {
                // inner not nullable - meaning always nullable
                if self.nullability(self.get_left(node_id)) == Nullability::NEVER {
                    (0, u32::MAX)
                } else {
                    (1, u32::MAX) // overapproximation
                }
            }
            Kind::Lookbehind => {
                (0, u32::MAX) // overapproximation
            }
            Kind::Lookahead => {
                (0, u32::MAX) // overapproximation
            }
            Kind::Lookaround => self.get_min_max_len_both(NodeId(self.get_extra(node_id))),
        }
    }

    fn is_star(&mut self, node_id: NodeId) -> bool {
        self.get_node_kind(node_id) == Kind::Loop
            && self.get_right(node_id).0 == 0
            && self.get_node(node_id).extra == u32::MAX
    }

    #[inline(always)]
    fn is_top(&mut self, node_id: NodeId) -> bool {
        node_id == NodeId::TOP
    }

    fn starts_with_ts(&mut self, node_id: NodeId) -> bool {
        if node_id == NodeId::TOPSTAR {
            return true;
        }
        match self.get_node_kind(node_id) {
            Kind::Inter => {
                self.starts_with_ts(self.get_left(node_id))
                    && self.starts_with_ts(self.get_right(node_id))
            }
            Kind::Union => {
                self.starts_with_ts(self.get_left(node_id))
                    && self.starts_with_ts(self.get_right(node_id))
            }
            Kind::Concat => self.starts_with_ts(self.get_left(node_id)),
            Kind::Loop => self.starts_with_ts(self.get_left(node_id)),
            _ => false,
        }
    }

    #[inline(always)]
    pub fn is_nullable(&mut self, node_id: NodeId, nullable_mask: Nullability) -> bool {
        debug_assert!(node_id != NodeId::MISSING);
        self.nullability(node_id).0 & nullable_mask.0 == nullable_mask.0
    }

    #[inline(always)]
    pub fn is_any_nullable(&mut self, node_id: NodeId) -> bool {
        debug_assert!(node_id != NodeId::MISSING);
        self.nullability(node_id) != Nullability::NEVER
    }

    #[inline(always)]
    pub fn is_begin_nullable(&mut self, node_id: NodeId) -> bool {
        debug_assert!(node_id != NodeId::MISSING);
        self.get_meta_flags(node_id).0 & MetaFlags::BEGIN_NULLABLE.0 == MetaFlags::BEGIN_NULLABLE.0
    }

    #[inline(always)]
    pub fn is_center_nullable(&mut self, node_id: NodeId) -> bool {
        debug_assert!(node_id != NodeId::MISSING);
        self.get_meta_flags(node_id).0 & MetaFlags::CENTER_NULLABLE.0
            == MetaFlags::CENTER_NULLABLE.0
    }

    #[inline(always)]
    pub fn cache_der(&mut self, node_id: NodeId, result: TRegexId, mask: Nullability) -> TRegexId {
        if mask == Nullability::CENTER {
            self.tr_der_center[node_id.0 as usize] = result;
        }
        result
    }

    pub fn der(&mut self, node_id: NodeId, mask: Nullability) -> TRegexId {
        if mask == Nullability::CENTER {
            match self.tr_der_center.get(node_id.0 as usize) {
                Some(&result) => {
                    if result != TRegexId::MISSING {
                        return result;
                    }
                }
                None => {
                    self.tr_der_center
                        .resize(self.array.len() as usize + 1, TRegexId::MISSING);
                }
            }
        }

        let result = match self.get_node_kind(node_id) {
            Kind::Compl => {
                let leftd = self.der(self.get_left(node_id), mask);
                self.tr_mk_compl(leftd)
            }
            Kind::Inter => {
                let leftd = self.der(self.get_left(node_id), mask);
                let rightd = self.der(self.get_right(node_id), mask);
                let result = self.tr_mk_inter(leftd, rightd);
                result
            }
            Kind::Union => {
                let leftd = self.der(self.get_left(node_id), mask);
                let rightd = self.der(self.get_right(node_id), mask);
                self.tr_mk_union(leftd, rightd)
            }
            Kind::Concat => {
                let left = self.get_left(node_id);
                let leftd = self.der(left, mask);
                let right = self.get_right(node_id);

                if self.is_nullable(left, mask) {
                    let rightd = self.der(right, mask);
                    let ldr = self.tr_mk_concat(leftd, right);
                    let union = self.tr_mk_union(ldr, rightd);
                    union
                } else {
                    let cat = self.tr_mk_concat(leftd, right);
                    cat
                }
            }
            Kind::Loop => {
                let left = self.get_left(node_id);
                let lower = self.get_right(node_id);
                let upper = self.get_node(node_id).extra;

                let new_lower = if lower.0 == u32::MAX || lower.0 == 0 {
                    lower.0
                } else {
                    lower.0 - 1
                };
                let new_upper = if upper == u32::MAX || upper == 0 {
                    upper
                } else {
                    upper - 1
                };
                let r_decr = self.mk_loop(left, new_lower, new_upper);
                let r_der = self.der(left, mask);
                let result = self.tr_mk_concat(r_der, r_decr);
                result
            }
            Kind::Lookaround => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);

                if left == NodeId::MISSING {
                    let bodynode = NodeId(self.get_node(node_id).extra);
                    let bodyd = self.der(bodynode, mask);
                    if self.is_nullable(bodynode, mask) {
                        let rightd = self.der(right, mask);
                        let ldr = self.tr_lookaround_wrap_2(bodyd, right);
                        self.tr_mk_union(ldr, rightd)
                    } else {
                        self.tr_lookaround_wrap_2(bodyd, right)
                    }
                } else {
                    let body = self.get_node(node_id).extra;
                    let leftd = self.der(left, mask);
                    let ldr = self.tr_lookaround_wrap_1(leftd, NodeId(body), right);
                    if self.is_nullable(left, mask) {
                        let tail = self.mk_lookaround(NodeId::MISSING, NodeId(body), right);
                        let rightd = self.der(tail, mask);
                        self.tr_mk_union(ldr, rightd)
                    } else {
                        ldr
                    }
                }
            }
            Kind::Lookbehind => {
                let left = self.get_left(node_id);
                let lder = self.der(left, mask);
                self.tr_mk_lookbehind(lder)
            }
            Kind::Lookahead => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                let rder = self.der(left, mask);
                let la = self.tr_mk_lookahead(rder, (right.0) + 1);
                la
            }
            Kind::Eps | Kind::Begin | Kind::End => TRegexId::BOT,
            Kind::Pred => {
                let psi = self.get_pred_tset(node_id);
                if self.solver().is_empty_id(psi) {
                    TRegexId::BOT
                } else {
                    self.mk_ite(psi, TRegexId::EPS, TRegexId::BOT)
                }
            }
        };
        self.cache_der(node_id, result, mask);
        result
    }

    pub fn get_pending_nullable(&mut self, node_id: NodeId, mask: Nullability) -> u32 {
        if !self.is_nullable(node_id, mask) {
            return u32::MAX;
        }

        let result = match self.get_node_kind(node_id) {
            Kind::Lookaround => {
                let la = self.get_right(node_id);
                let rel_to = self.get_node(la).right;
                rel_to.0
            }
            Kind::Union | Kind::Inter => min(
                self.get_pending_nullable(self.get_left(node_id), mask),
                self.get_pending_nullable(self.get_right(node_id), mask),
            ),
            Kind::Loop | Kind::Compl | Kind::Eps | Kind::Concat | Kind::End => return 0,
            _ => {
                panic!("unexpected node kind: {:?}", self.get_node_kind(node_id));
            }
        };
        result
    }

    fn init(&mut self, inst: Node) -> NodeId {
        self.num_created += 1;
        let new_id = NodeId(self.num_created);
        self.cache.insert(inst.clone(), new_id);
        self.array.push(inst);
        new_id
    }

    fn get_node_id(&mut self, inst: Node) -> NodeId {
        match self.cache.get(&inst) {
            Some(&id) => id,
            None => self.init(inst),
        }
    }
    #[inline]
    fn key_is_created(&self, inst: &Node) -> Option<&NodeId> {
        self.cache.get(inst)
    }

    #[inline]
    fn override_key(&mut self, key: Node, subsumed: NodeId) -> NodeId {
        self.cache.insert(key, subsumed);
        subsumed
    }

    #[inline]
    pub fn get_left(&self, node_id: NodeId) -> NodeId {
        self.array[node_id.0 as usize].left
    }

    #[inline]
    pub fn get_right(&self, node_id: NodeId) -> NodeId {
        self.array[node_id.0 as usize].right
    }

    #[inline]
    pub fn get_extra(&self, node_id: NodeId) -> u32 {
        self.array[node_id.0 as usize].extra
    }

    #[inline]
    pub fn get_pred_tset(&self, node_id: NodeId) -> TSetId {
        debug_assert!(self.get_kind(node_id) == Kind::Pred);
        TSetId(self.get_extra(node_id))
    }

    #[inline]
    pub fn get_kind(&self, node_id: NodeId) -> Kind {
        self.array[node_id.0 as usize].kind
    }

    #[inline]
    pub fn get_node(&self, node_id: NodeId) -> &Node {
        &self.array[node_id.0 as usize]
    }

    #[inline]
    fn get_node_kind(&self, node_id: NodeId) -> Kind {
        self.array[node_id.0 as usize].kind
    }

    #[inline]
    fn get_node_meta_id(&self, node_id: NodeId) -> MetadataId {
        (&self.array[node_id.0 as usize]).meta
    }

    #[inline]
    fn meta_contains_lookaround(&self, node_id: NodeId) -> bool {
        let metaid = (&self.array[node_id.0 as usize]).meta;
        self.mb.array[metaid.0 as usize]
            .flags
            .contains_lookaround()
            .0
            != 0
    }

    #[inline]
    fn meta_contains_lookbehind(&self, node_id: NodeId) -> bool {
        let metaid = (&self.array[node_id.0 as usize]).meta;
        self.mb.array[metaid.0 as usize].flags.contains_lb()
    }

    #[inline]
    fn get_meta(&self, node_id: NodeId) -> &Metadata {
        let meta_id = (&self.array[node_id.0 as usize]).meta;
        &self.mb.array[meta_id.0 as usize]
    }

    #[inline]
    pub fn get_meta_flags(&self, node_id: NodeId) -> MetaFlags {
        let meta_id = (&self.array[node_id.0 as usize]).meta;
        let meta = &self.mb.array[meta_id.0 as usize];
        meta.flags
    }

    #[inline]
    pub fn get_meta_nullability(&self, node_id: NodeId) -> Nullability {
        let nullability = self.get_meta(node_id).flags.nullability();
        nullability
    }

    #[inline]
    pub fn get_flags_nullability(&self, node_id: NodeId) -> MetaFlags {
        let nullability = self.get_meta(node_id).flags & MetaFlags::ALL_NULLABILITIES;
        nullability
    }

    pub fn reverse(&mut self, node_id: NodeId) -> NodeId {
        match self.get_kind(node_id) {
            Kind::End | Kind::Pred | Kind::Begin | Kind::Eps => node_id,
            Kind::Concat => {
                let left = self.reverse(self.get_left(node_id));
                let right = self.reverse(self.get_right(node_id));
                self.mk_concat(right, left)
            }
            Kind::Union => {
                let left = self.reverse(self.get_left(node_id));
                let right = self.reverse(self.get_right(node_id));
                self.mk_union(left, right)
            }
            Kind::Inter => {
                let left = self.reverse(self.get_left(node_id));
                let right = self.reverse(self.get_right(node_id));
                self.mk_inter(left, right)
            }
            Kind::Loop => {
                let body = self.reverse(self.get_left(node_id));
                let lower = self.get_right(node_id).0;
                let upper = self.get_extra(node_id);
                self.mk_loop(body, lower, upper)
            }
            Kind::Compl => {
                let body = self.reverse(self.get_left(node_id));
                self.mk_compl(body)
            }
            Kind::Lookbehind => {
                unimplemented!("lookbehind reversal not implemented");
            }
            Kind::Lookahead => {
                unimplemented!("lookahead reversal not implemented");
            }
            Kind::Lookaround => {
                unimplemented!("lookaround reversal not implemented");
            }
        }
    }

    pub fn is_null_lb_center(&mut self, node_id: NodeId) -> bool {
        if self.get_node_kind(node_id) != Kind::Lookaround {
            return false;
        }
        let left = self.get_left(node_id);
        if NodeId::MISSING == left {
            return false;
        } else {
            self.is_nullable(left, Nullability::CENTER)
        }
    }

    pub fn is_null_lb_begin(&mut self, node_id: NodeId) -> bool {
        if self.get_node_kind(node_id) != Kind::Lookaround {
            return false;
        }
        let left = self.get_left(node_id);
        if NodeId::MISSING == left {
            return false;
        } else {
            self.is_nullable(left, Nullability::BEGIN)
        }
    }

    pub fn build_flags_null_lookbehind(&self, node_id: NodeId) -> MetaFlags {
        let nullability = self.get_meta(node_id).flags & MetaFlags::ALL_NULLABILITIES;
        nullability | MetaFlags::CONTAINS_LOOKAROUND | MetaFlags::CONTAINS_LOOKBEHIND
    }

    pub fn get_lookbehind_flags(&self, node_id: NodeId) -> MetaFlags {
        if node_id == NodeId::MISSING {
            return MetaFlags::ZERO;
        }
        let nullability = self.get_meta(node_id).flags & (MetaFlags::CONTAINS_LOOKBEHIND);
        nullability
    }

    pub fn mk_eps(&mut self, eps_tag: u32) -> NodeId {
        let metaid = self.mb.get_meta_id(Metadata {
            flags: self.mb.flags_eps(),
        });
        let node = Node {
            kind: Kind::Eps,
            left: NodeId::MISSING,
            right: NodeId::MISSING,
            extra: eps_tag,
            meta: metaid,
        };
        self.get_node_id(node)
    }

    pub fn mk_pred(&mut self, pred: TSetId) -> NodeId {
        let metaid = self.mb.get_meta_id(Metadata {
            flags: self.mb.flags_pred(),
        });
        let node = Node {
            kind: Kind::Pred,
            left: NodeId::MISSING,
            right: NodeId::MISSING,
            extra: pred.0,
            meta: metaid,
        };
        self.get_node_id(node)
    }

    pub fn mk_compl(&mut self, body_id: NodeId) -> NodeId {
        if body_id == NodeId::BOT {
            return NodeId::TOPSTAR;
        }
        if body_id == NodeId::TOPSTAR {
            return NodeId::BOT;
        }
        if self.get_node_kind(body_id) == Kind::Compl {
            return self.get_node(body_id).left;
        }
        if self.get_node_kind(body_id) == Kind::Lookaround {
            // NOT-ELIM
            let lookbehind = self.get_left(body_id);
            let body = NodeId(self.get_extra(body_id));
            let not_body = self.mk_compl(body);
            let lookahead = self.get_right(body_id);
            let rw_lookbehind = if lookbehind == NodeId::MISSING {
                NodeId::BOT
            } else {
                let lb_body = self.get_left(lookbehind);
                assert!(
                    !self.contains_look(lb_body),
                    "this node has to be converted to Lookaround Normal Form: {}",
                    self.pp(lookbehind)
                );
                let neg_lb = self.mk_neg_lookbehind(lb_body);
                self.mk_concat(neg_lb, NodeId::TOPSTAR)
            };
            let rw_lookahead = if lookahead == NodeId::MISSING {
                NodeId::BOT
            } else {
                let la_body = self.get_left(lookahead);
                assert!(
                    !self.contains_look(la_body),
                    "this node has to be converted to Lookaround Normal Form: {}",
                    self.pp(lookahead)
                );
                let neg_la = self.mk_neg_lookahead(la_body);
                self.mk_concat(neg_la, NodeId::TOPSTAR)
            };
            let new_node = self.mk_unions([rw_lookbehind, not_body, rw_lookahead].into_iter());
            return new_node;
        }

        let metaid = self.mb.get_meta_id(Metadata {
            flags: self.mb.flags_compl(self.get_node_meta_id(body_id)),
        });
        let node = Node {
            kind: Kind::Compl,
            left: body_id,
            right: NodeId::MISSING,
            extra: u32::MAX,
            meta: metaid,
        };
        let node_id = self.get_node_id(node);
        // compare to _* eagerly so we can short-circuit
        // based on this later in is_empty_lang
        if self.is_any_nullable(body_id) && self.is_full_lang(body_id) {
            return NodeId::BOT;
        }
        node_id
    }

    fn mk_concat_key(&mut self, head: NodeId, tail: NodeId) -> Node {
        let hid = self.get_node_meta_id(head);
        let tid = self.get_node_meta_id(tail);
        let metaid = self.mb.merge_concat(hid, tid);
        let node = Node {
            kind: Kind::Concat,
            left: head,
            right: tail,
            extra: u32::MAX,
            meta: metaid,
        };
        node
    }

    pub fn mk_concat(&mut self, head: NodeId, tail: NodeId) -> NodeId {
        debug_assert!(self.get_node_kind(head) != Kind::Lookbehind);
        debug_assert!(self.get_node_kind(tail) != Kind::Lookahead);
        match head {
            NodeId::EPS => return tail,
            NodeId::BOT => return NodeId::BOT,
            NodeId::END => {
                if !self.is_nullable(tail, Nullability::END) {
                    return NodeId::BOT;
                } else {
                    return NodeId::END;
                }
            }
            _ => {}
        }
        match tail {
            NodeId::EPS => return head,
            NodeId::BOT => return NodeId::BOT,
            NodeId::BEGIN => {
                if !self.is_nullable(head, Nullability::BEGIN) {
                    return NodeId::BOT;
                } else {
                    return NodeId::BEGIN;
                }
            }
            _ => {}
        }
        if head == tail {
            return self.mk_loop(head, 2, 2);
        }

        let key = self.mk_concat_key(head, tail);
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        // normalize, concat always in tail
        if self.get_node_kind(head) == Kind::Concat {
            match self.get_kind(tail) {
                // also increment loops opportunistically
                Kind::Loop if head == self.get_left(tail) => {
                    let new_node =
                        self.mk_loop(head, self.get_right(tail).0 + 1, self.get_extra(tail) + 1);
                    return new_node;
                }

                _ => {
                    let left = self.get_left(head);
                    let newright = self.mk_concat(self.get_right(head), tail);
                    return self.mk_concat(left, newright);
                }
            }
        }
        if self.meta_contains_lookaround(tail) && self.get_node_kind(tail) != Kind::Lookaround {
            match self.get_node_kind(tail) {
                Kind::Inter => {
                    // if there are no lookbehinds on tail then can support
                    if !self.meta_contains_lookbehind(tail) {
                        return self.init(key);
                    }
                    panic!("unsupported lookaround in inter");
                }
                Kind::Concat => {
                    // if there are no lookbehinds on tail then can support
                    if !self.meta_contains_lookbehind(tail) {
                        return self.init(key);
                    }
                }
                _ => {
                    unimplemented!("unsupported lookaround rewrite")
                }
            }
        }
        // lookaround rewrites head, but not tail
        if self.meta_contains_lookaround(head) && self.get_node_kind(head) != Kind::Lookaround {
            match self.get_node_kind(head) {
                Kind::Loop => {
                    if self.get_kind(tail) == Kind::Lookaround {
                        debug_assert!(self.get_left(tail) == NodeId::MISSING);
                        debug_assert!(NodeId(self.get_extra(tail)) == NodeId::EPS);
                        let lookahead = self.get_right(tail);
                        return self.mk_lookaround(NodeId::MISSING, head, lookahead);
                    }
                    return self.init(key);
                }
                Kind::Union => {
                    let c1 = self.mk_concat(self.get_node(head).left, tail);
                    let c2 = self.mk_concat(self.get_node(head).right, tail);
                    return self.mk_union(c1, c2);
                }
                _ => {
                    unimplemented!("unsupported lookaround rewrite")
                }
            }
        }

        match (self.get_kind(head), self.get_kind(tail)) {
            // merge stars
            (Kind::Loop, Kind::Concat) if self.is_star(head) => {
                let rl = self.get_left(tail);
                if head == rl {
                    return tail; // .*.*ab -> .*ab
                }
                if head == NodeId::TOPSTAR {
                    let tail_head = self.get_left(tail);
                    let min_len = self.get_min_length_only(tail_head);
                    if min_len == 0 {
                        let new_node = self.mk_concat(head, self.get_right(tail));
                        return self.override_key(key, new_node);
                    } else {
                        // if tail starts with _* then head is not needed
                        if self.starts_with_ts(tail_head) {
                            return tail;
                        }
                    }
                } else {
                }
            }
            _ if head == NodeId::TOPSTAR => {
                if self.starts_with_ts(tail) {
                    return tail;
                }
            }
            _ => {}
        }

        // this defines what kind of lookarounds are allowed
        // if a rewrite is needed, it should be done here
        // formally, only (?<=B)E(?=A) 3-tuples are supported
        match (self.get_node_kind(head), self.get_node_kind(tail)) {
            (Kind::Lookaround, Kind::Lookaround) => {
                let headlb = self.get_node(head).left;
                let taillb = self.get_node(tail).left;
                debug_assert!(taillb == NodeId::MISSING, "lookaround rewrite needed");
                let headla = self.get_node(head).right;
                let tailla = self.get_node(tail).right;
                // best case, no rewrites needed
                if headla == NodeId::MISSING {
                    let new_concat = self.mk_concat(
                        NodeId(self.get_node(head).extra),
                        NodeId(self.get_node(tail).extra),
                    );
                    return self.mk_lookaround(headlb, new_concat, tailla);
                }
                if headla != NodeId::MISSING {
                    let lookahead_body = self.get_node(headla).left;
                    let la_ts = self.mk_concat(lookahead_body, NodeId::TOPSTAR);
                    let newtail = self.mk_inter(la_ts, NodeId(self.get_node(tail).extra));
                    let new_concat = self.mk_concat(NodeId(self.get_node(head).extra), newtail);
                    return self.mk_lookaround(headlb, new_concat, tailla);
                }
            }
            _ => {}
        }

        self.init(key)
    }

    pub fn mk_lookbehind(&mut self, body: NodeId) -> NodeId {
        debug_assert!(body != NodeId::MISSING);
        if body == NodeId::BOT {
            return NodeId::BOT;
        }
        if body == NodeId::TOPSTAR {
            return NodeId::EPS;
        }
        if body == NodeId::EPS {
            return NodeId::EPS;
        }
        let flags = self.build_flags_null_lookbehind(body);
        let metaid = self.mb.get_meta_id(Metadata { flags });
        let node = Node {
            kind: Kind::Lookbehind,
            left: body,
            right: NodeId::MISSING,
            extra: u32::MAX,
            meta: metaid,
        };
        let lookbehind_id = self.get_node_id(node);
        // never return a lookbehind, return lookaround node instead
        self.mk_lookaround(lookbehind_id, NodeId::EPS, NodeId::MISSING)
    }

    pub fn mk_neg_lookahead(&mut self, body: NodeId) -> NodeId {
        match self.get_node(body).kind {
            Kind::Pred => {
                let psi = self.get_pred_tset(body);
                let negated = self.mk_pred_not(psi);
                let union = self.mk_union(NodeId::END, negated);
                let la = self.mk_lookahead(union, 0);
                la
            }
            _ => {
                let neg_inner = self.mk_concat(body, NodeId::TOPSTAR);
                let neg_part = self.mk_compl(neg_inner);
                let conc = self.mk_concat(neg_part, NodeId::END);
                let look = self.mk_lookahead(conc, 0);
                look
            }
        }
    }

    pub fn mk_neg_lookbehind(&mut self, body: NodeId) -> NodeId {
        match self.get_node(body).kind {
            Kind::Pred => {
                let psi = self.get_pred_tset(body);
                let negated = self.mk_pred_not(psi);
                let union = self.mk_union(NodeId::BEGIN, negated);
                let lb = self.mk_lookbehind(union);
                lb
            }
            _ => {
                let neg_inner = self.mk_concat(NodeId::TOPSTAR, body);
                let neg_part = self.mk_compl(neg_inner);
                let conc = self.mk_concat(NodeId::BEGIN, neg_part);
                let look = self.mk_lookbehind(conc);
                look
            }
        }
    }

    pub fn mk_lookahead(&mut self, body: NodeId, rel: u32) -> NodeId {
        // lookahead cannot contain lookaround
        debug_assert!(self.meta_contains_lookaround(body) == false);
        debug_assert!(body != NodeId::MISSING);
        if body == NodeId::BOT {
            return NodeId::BOT;
        }
        let metaid = self.mb.get_meta_id(Metadata {
            flags: self.mb.flags_look(self.get_flags_nullability(body)),
        });
        let node = Node {
            kind: Kind::Lookahead,
            left: body,
            right: NodeId(rel),
            extra: u32::MAX,
            meta: metaid,
        };
        let lookahead_id = self.get_node_id(node);
        // never return a lookahead, return lookaround node instead
        self.mk_lookaround(NodeId::MISSING, NodeId::EPS, lookahead_id)
    }

    pub fn mk_lookaround(
        &mut self,
        look_behind: NodeId,
        body: NodeId,
        look_ahead: NodeId,
    ) -> NodeId {
        if look_behind == NodeId::BOT || body == NodeId::BOT || look_ahead == NodeId::BOT {
            return NodeId::BOT;
        }
        let lb = if look_behind == NodeId::EPS {
            NodeId::MISSING
        } else {
            look_behind
        };
        let la = look_ahead;
        if self.get_node_kind(lb) == Kind::Lookaround {
            let lblb = self.get_node(lb);
            if lblb.right == NodeId::MISSING && lblb.extra == id::EPS {
                return self.mk_lookaround(lblb.left, body, la);
            }
            panic!("unsupported pattern for lookbehind");
        }

        debug_assert!(lb == NodeId::MISSING || self.get_node_kind(lb) == Kind::Lookbehind);
        debug_assert!(
            la == NodeId::MISSING || self.get_node_kind(la) == Kind::Lookahead,
            "{:?}",
            self.pp(la)
        );
        debug_assert!(
            self.get_node_kind(body) != Kind::Lookahead
                && self.get_node_kind(body) != Kind::Lookbehind
        );
        if lb == NodeId::MISSING && la == NodeId::MISSING {
            return body;
        }
        let nullabilities = self.get_flags_nullability(lb)
            & self.get_flags_nullability(body)
            & self.get_flags_nullability(la);
        let lbnull = self.get_lookbehind_flags(lb);

        let flags = self.mb.flags_look(nullabilities | lbnull);
        let metaid = self.mb.get_meta_id(Metadata { flags });

        let node = Node {
            kind: Kind::Lookaround,
            left: lb,
            right: la,
            extra: body.0,
            meta: metaid,
        };

        let new_id = self.get_node_id(node);
        new_id
    }

    fn collect_unions(&self, node_id: NodeId) -> Vec<NodeId> {
        let mut stack = Vec::new();
        let mut result = Vec::new();
        stack.push(node_id);
        while let Some(current) = stack.pop() {
            match self.get_node(current) {
                Node {
                    kind: Kind::Union,
                    left: l,
                    right: r,
                    ..
                } => {
                    stack.push(*l);
                    stack.push(*r);
                }
                _ => {
                    result.push(current);
                }
            }
        }
        result
    }

    fn mk_union_key(&mut self, left: NodeId, right: NodeId) -> Node {
        debug_assert!(left.0 <= right.0);
        let m1 = self.get_node_meta_id(left);
        let m2 = self.get_node_meta_id(right);
        let meta = self.mb.merge_union(m1, m2);
        let node = Node {
            kind: Kind::Union,
            left,
            right,
            extra: u32::MAX,
            meta,
        };
        node
    }

    pub fn concat_to_vec(&mut self, concat: NodeId) -> Vec<NodeId> {
        let mut result = Vec::new();
        let mut current = concat;
        while self.get_node_kind(current) == Kind::Concat {
            result.push(self.get_left(current));
            current = self.get_right(current);
        }
        result.push(current);
        result
    }

    pub fn mk_union(&mut self, orig_left: NodeId, orig_right: NodeId) -> NodeId {
        debug_assert!(orig_left != NodeId::MISSING);
        debug_assert!(orig_right != NodeId::MISSING);
        if orig_left == orig_right {
            return orig_left;
        }
        if orig_left == NodeId::BOT {
            return orig_right;
        }
        if orig_right == NodeId::BOT {
            return orig_left;
        }
        if orig_left == NodeId::TOPSTAR || orig_right == NodeId::TOPSTAR {
            return NodeId::TOPSTAR;
        }
        let (left_id, right_id) = self.in_order(orig_left, orig_right);

        // short-circuit if overridden
        // let pending_id = self.mk_union_key(left_id, right_id);
        let key = self.mk_union_key(left_id, right_id);
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        // common kind rules; always apply
        match (self.get_node_kind(left_id), self.get_node_kind(right_id)) {
            (Kind::Pred, Kind::Pred) => {
                let psi1 = self.get_pred_tset(left_id);
                let psi2 = self.get_pred_tset(right_id);
                let psi = self.solver().or_id(psi1, psi2);
                let rewrite = self.mk_pred(psi);
                return self.override_key(key, rewrite);
            }
            (Kind::Compl, _) if self.get_left(left_id) == right_id => {
                return self.override_key(key, NodeId::TOPSTAR);
            }
            (_, Kind::Compl) if self.get_left(right_id) == left_id => return NodeId::TOPSTAR,
            (Kind::Loop, Kind::Loop) => {
                if self.get_left(left_id) == self.get_left(right_id) {
                    let leftlow = self.get_node(left_id).right.0;
                    let leftup = self.get_node(left_id).extra;
                    let rightlow = self.get_node(right_id).right.0;
                    let rightup = self.get_node(right_id).extra;
                    let new_low = leftlow.min(rightlow);
                    let new_up = leftup.max(rightup);
                    let rewrite = self.mk_loop(self.get_left(left_id), new_low, new_up);
                    return self.override_key(key, rewrite);
                }
            }
            (Kind::Loop, Kind::Union) if self.get_kind(self.get_left(right_id)) == Kind::Loop => {
                let rloop = self.get_left(right_id);
                if self.get_left(left_id) == self.get_left(rloop) {
                    let leftlow = self.get_node(left_id).right.0;
                    let leftup = self.get_node(left_id).extra;
                    let rightlow = self.get_node(rloop).right.0;
                    let rightup = self.get_node(rloop).extra;
                    let new_low = leftlow.min(rightlow);
                    let new_up = leftup.max(rightup);
                    let new_loop = self.mk_loop(self.get_left(left_id), new_low, new_up);
                    let rewrite = self.mk_union(new_loop, self.get_right(right_id));
                    return self.override_key(key, rewrite);
                }
                if self.subsumes(rloop, left_id) {
                    return self.override_key(key, right_id);
                }
                if self.subsumes(left_id, rloop) {
                    let rewrite = self.mk_union(left_id, self.get_right(right_id));
                    return self.override_key(key, rewrite);
                }
            }
            // ([^n]{0,33}&_{8,})|([^n]{0,29}&_{8,})
            (Kind::Inter, Kind::Union) if self.get_kind(self.get_left(right_id)) == Kind::Inter => {
                // if the right side of both unions is the same, we can simplify
                let linter = left_id; // [^n]{0,33}&_{8,}
                let rinter = self.get_left(right_id); // [^n]{0,29}&_{8,}
                                                      // if _{8,} == _{8,}
                if self.get_right(linter) == self.get_right(rinter) {
                    // try merge the left sides
                    let lleft = self.get_left(linter);
                    let rleft = self.get_left(rinter);
                    let new_left = self.mk_union(lleft, rleft);
                    let inorder_key = self.in_order(lleft, rleft);
                    let expected_left = self.mk_union_key(inorder_key.0, inorder_key.1);
                    let new_left_node = self.get_node(new_left);
                    // only rewrite intersection if a rewrite happened on the left side
                    // otherwise we prefer DNF over CNF
                    if *new_left_node != expected_left {
                        let new_right = self.get_right(rinter);
                        // [^n]{0,29}|[^n]{0,33} & _{8,}
                        let rewrite = self.mk_inter(new_left, new_right);
                        return self.override_key(key, rewrite);
                    }
                }
            }
            _ => {}
        }

        // common duplicate
        if self.get_node_kind(orig_right) == Kind::Union && orig_left == self.get_left(orig_right) {
            return orig_right;
        }

        match (self.get_node(left_id), self.get_node(right_id)) {
            // there should never be union on left
            (
                Node {
                    kind: Kind::Union, ..
                },
                _,
            ) => {
                let mut set = BTreeSet::new();
                let mut stack = Vec::new();
                stack.push(left_id);
                stack.push(right_id);
                while let Some(current) = stack.pop() {
                    match self.get_node(current) {
                        Node {
                            kind: Kind::Union,
                            left: l,
                            right: r,
                            ..
                        } => {
                            stack.push(*l);
                            stack.push(*r);
                        }
                        _ => {
                            set.insert(current);
                        }
                    }
                }
                let newnode = self.mk_unions_set(set);
                self.override_key(key, newnode);
                return newnode;
            }
            // merging concat tries ab|ac -> a(b|c)
            (
                Node {
                    kind: Kind::Concat, ..
                },
                Node {
                    kind: Kind::Concat, ..
                },
            ) => {
                if self.get_left(left_id) == self.get_left(right_id) {
                    let left = self.get_node(left_id).right;
                    let right = self.get_node(right_id).right;
                    let new_right = self.mk_union(left, right);
                    return self.mk_concat(self.get_left(left_id), new_right);
                } else {
                    let conc_l = self.concat_to_vec(left_id);
                    let conc_r = self.concat_to_vec(right_id);
                    let mut new_tail = NodeId::EPS;
                    let min_len = min(conc_l.len(), conc_r.len());
                    let mut rev_idx = 0;
                    for i in 0..min_len {
                        rev_idx = i + 1;
                        let cl = conc_l[conc_l.len() - rev_idx];
                        let cr = conc_r[conc_r.len() - rev_idx];
                        if cl == cr {
                            new_tail = self.mk_concat(cl, new_tail);
                        } else {
                            rev_idx -= 1;
                            break;
                        }
                    }
                    if new_tail != NodeId::EPS {
                        let head1 = self.mk_concats_slice(&conc_l[..conc_l.len() - rev_idx]);
                        let head2 = self.mk_concats_slice(&conc_r[..conc_r.len() - rev_idx]);
                        let new_head = self.mk_union(head1, head2);
                        return self.mk_concat(new_head, new_tail);
                    } else {
                    }
                }
            }

            // loop simplification
            (
                left_node,
                Node {
                    kind: Kind::Union,
                    left: rleft,
                    right: rright,
                    ..
                },
            ) if left_node.kind != Kind::Union && self.get_node(*rright).kind != Kind::Union => {
                // duplicate
                if left_id == *rleft {
                    return right_id;
                }
                if left_id < *rleft {
                } else {
                    let mut nodes = BTreeSet::new();
                    nodes.insert(left_id);
                    nodes.insert(*rleft);
                    nodes.insert(*rright);
                    let mut new_union = NodeId::BOT;
                    for node in nodes.iter().rev() {
                        new_union = self.mk_union(*node, new_union);
                    }
                    return new_union;
                }
            }
            (
                left_node,
                Node {
                    kind: Kind::Union,
                    left: rleft,
                    right: rright,
                    ..
                },
            ) if left_node.kind != Kind::Union => {
                // duplicate
                if left_id == *rleft {
                    return right_id;
                }
                // if left_node id is smaller than rleft, just create a new union
                if left_id > *rleft {
                    // collect all the nodes
                    let mut nodes = BTreeSet::new();
                    nodes.insert(left_id);
                    self.collect_unions(*rleft).iter().for_each(|x| {
                        nodes.insert(*x);
                    });
                    self.collect_unions(*rright).iter().for_each(|x| {
                        nodes.insert(*x);
                    });
                    // construct the new union
                    let mut new_union = NodeId::BOT;
                    for node in nodes.iter().rev() {
                        new_union = self.mk_union(*node, new_union);
                    }
                    return new_union;
                } else {
                }
            }
            _ => {}
        };
        self.init(key)
    }

    pub fn mk_inter_key(&mut self, left: NodeId, right: NodeId) -> Node {
        debug_assert!(left.0 <= right.0);
        let m1 = self.get_node_meta_id(left);
        let m2 = self.get_node_meta_id(right);
        let meta = self.mb.merge_inter(m1, m2);
        let node = Node {
            kind: Kind::Inter,
            left,
            right,
            extra: u32::MAX,
            meta,
        };
        node
    }

    pub fn mk_inter(&mut self, orig_left: NodeId, orig_right: NodeId) -> NodeId {
        debug_assert!(orig_left != NodeId::MISSING);
        debug_assert!(orig_right != NodeId::MISSING);
        if orig_left == orig_right {
            return orig_left;
        }
        if orig_left == NodeId::BOT || orig_right == NodeId::BOT {
            return NodeId::BOT;
        }
        if orig_left == NodeId::TOPSTAR {
            return orig_right;
        }
        if orig_right == NodeId::TOPSTAR {
            return orig_left;
        }
        let (left_id, right_id) = self.in_order(orig_left, orig_right);

        let key = self.mk_inter_key(left_id, right_id);
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }
        let leftkind = self.get_node_kind(left_id);
        let rightkind = self.get_node_kind(right_id);

        if leftkind == Kind::Pred && rightkind == Kind::Compl {
            // common case for pred compl
            if self.get_kind(self.get_left(right_id)) == Kind::Pred {
                let psi1 = self.get_pred_tset(left_id);
                let psi2 = self.get_pred_tset(self.get_left(right_id));
                let notpsi2 = self.solver().not_id(psi2);
                let andpsi = self.solver().and_id(psi1, notpsi2);
                let rewrite = self.mk_pred(andpsi);
                return self.override_key(key, rewrite);
            }
        }

        // common kind rules; always apply
        match (leftkind, rightkind) {
            (Kind::Eps, _) => match self.nullability(right_id) {
                Nullability::ALWAYS => return NodeId::EPS,
                Nullability::NEVER => return NodeId::BOT,
                Nullability::BEGIN => return NodeId::BEGIN,
                Nullability::END => return NodeId::END,
                _ => {}
            },
            // self-complement
            (Kind::Compl, _) if self.get_left(left_id) == right_id => return NodeId::BOT,
            (_, Kind::Compl) if self.get_left(right_id) == left_id => return NodeId::BOT,
            // predicates
            (Kind::Pred, Kind::Pred) => {
                let psi1 = self.get_pred_tset(left_id);
                let psi2 = self.get_pred_tset(right_id);
                let pred = self.solver().and_id(psi1, psi2);
                let rewrite = self.mk_pred(pred);
                self.override_key(key, rewrite);
                return rewrite;
            }
            (Kind::Pred, Kind::Compl) if self.get_kind(self.get_left(right_id)) == Kind::Pred => {
                let psi1 = self.get_pred_tset(left_id);
                let psi2 = self.get_pred_tset(self.get_left(right_id));
                let notpsi2 = self.solver().not_id(psi2);
                let pred = self.solver().and_id(psi1, notpsi2);
                let rewrite = self.mk_pred(pred);
                self.override_key(key, rewrite);
                return rewrite;
            }
            // lookaround rules
            (Kind::Lookaround, rkind) => {
                let lb = self.get_left(left_id);
                let le = NodeId(self.get_extra(left_id));
                let la = self.get_right(left_id);
                
                match rkind {
                    Kind::Lookaround => {
                        let rb = self.get_left(right_id);
                        let re = NodeId(self.get_extra(right_id));
                        let ra = self.get_right(right_id);
                        let new_b = self.mk_inter(lb.missing_to_ts(), rb.missing_to_ts());
                        let new_e = self.mk_inter(le, re);
                        let new_a = self.mk_inter(la.missing_to_ts(), ra.missing_to_ts());
                        self.mk_lookaround(new_b, new_e, new_a);
                    }
                    _ => {
                        let new_inter = self.mk_inter(le, right_id);
                        return self.mk_lookaround(lb, new_inter, la);
                    }
                }
            }
            (_, Kind::Lookaround) => {
                let rb = self.get_left(right_id);
                let re = NodeId(self.get_extra(right_id));
                let ra = self.get_right(right_id);
                let new_inter = self.mk_inter(left_id, re);
                return self.mk_lookaround(rb, new_inter, ra);
            }
            // distribute union
            (_, Kind::Union) if self.meta_contains_lookaround(right_id) => {
                let unions = self.collect_unions(right_id);
                let mut result = NodeId::BOT;
                unions.iter().for_each(|x| {
                    let new_inter = self.mk_inter(left_id, *x);
                    result = self.mk_union(result, new_inter)
                });
                return result;
            }
            (Kind::Union, _) if self.meta_contains_lookaround(left_id) => {
                let unions = self.collect_unions(left_id);
                let mut result = NodeId::BOT;
                unions.iter().for_each(|x| {
                    let new_inter = self.mk_inter(right_id, *x);
                    result = self.mk_union(result, new_inter)
                });
                return result;
            }
            // check length constraints satisfiable
            (lk, Kind::Loop) if lk != Kind::Loop && self.is_top(self.get_left(right_id)) => {
                let minmaxr = self.get_min_max_len(right_id);
                let minmaxl = self.get_min_max_len(left_id);
                if self.unsat_lengths(minmaxl, minmaxr) {
                    return self.override_key(key, NodeId::BOT);
                }
            }
            (Kind::Loop, rk) if rk != Kind::Loop && self.is_top(self.get_left(left_id)) => {
                let minmaxr = self.get_min_max_len(right_id);
                let minmaxl = self.get_min_max_len(left_id);
                if self.unsat_lengths(minmaxl, minmaxr) {
                    return self.override_key(key, NodeId::BOT);
                }
            }
            //// merge 2 loops; only true for pred
            (Kind::Loop, Kind::Loop) => {
                if self.get_left(left_id) == self.get_left(right_id) {
                    match self.get_kind(self.get_left(left_id)) {
                        Kind::Pred => {
                            let leftlow = self.get_node(left_id).right.0;
                            let leftup = self.get_node(left_id).extra;
                            let rightlow = self.get_node(right_id).right.0;
                            let rightup = self.get_node(right_id).extra;
                            let new_low = leftlow.max(rightlow);
                            let new_up = leftup.min(rightup);
                            if new_low > new_up {
                                return self.override_key(key, NodeId::BOT);
                            }
                            let new_loop = self.mk_loop(self.get_left(left_id), new_low, new_up);
                            return new_loop;
                        }
                        _ => {
                            // (_*a){20}" | "(_*a){30} -> (_*a){30}
                            let lbody = self.get_left(left_id);
                            if self.meta_is_infinite(lbody) {
                                // check if contains itself
                                let conc2 = self.mk_concat(lbody, lbody);
                                if self.subsumes(lbody, conc2) {
                                    let l_low = self.get_node(left_id).right.0;
                                    let r_low = self.get_node(right_id).right.0;
                                    if l_low > r_low {
                                        return left_id;
                                    } else {
                                        return right_id;
                                    }
                                }
                            }
                        }
                    }
                }
                // ([^n]{0,22}&_+)
                if self.get_kind(self.get_left(left_id)) == Kind::Pred
                    && self.get_kind(self.get_left(right_id)) == Kind::Pred
                {
                    let rbody = self.get_left(right_id);
                    let leftlow = self.get_node(left_id).right.0;
                    let leftup = self.get_node(left_id).extra;
                    let rightlow = self.get_node(right_id).right.0;
                    let rightup = self.get_node(right_id).extra;
                    if rbody == NodeId::TOP {
                        let new_low = leftlow.max(rightlow);
                        let new_up = leftup.min(rightup);
                        if new_low > new_up {
                            return self.override_key(key, NodeId::BOT);
                        }
                        let new_loop = self.mk_loop(self.get_left(left_id), new_low, new_up);
                        return self.override_key(key, new_loop);
                    }
                }
            }
            (Kind::Union, _) => {
                let left_unions = self.collect_unions(left_id);
                let mut result = NodeId::BOT;
                // distribute loop
                for u in left_unions.iter() {
                    let new_inter = self.mk_inter(*u, right_id);
                    result = self.mk_union(result, new_inter);
                }
                return self.override_key(key, result);
            }
            (_, Kind::Union) => {
                let right_unions = self.collect_unions(right_id);
                let mut result = NodeId::BOT;
                // distribute loop
                for u in right_unions.iter() {
                    let new_inter = self.mk_inter(*u, left_id);
                    result = self.mk_union(result, new_inter);
                }
                return self.override_key(key, result);
            }
            (_, _) if !self.meta_is_infinite(left_id) || !self.meta_is_infinite(right_id) => {
                let left_min_max = self.get_min_max_len(left_id);
                let right_min_max = self.get_min_max_len(right_id);
                if left_min_max.0 > right_min_max.1 || right_min_max.0 > left_min_max.1 {
                    return self.override_key(key, NodeId::BOT);
                }
            }
            _ => {
                // both guaranteed infinite length here
                match (self.get_kind(left_id), self.get_kind(right_id)) {
                    // R & R* -> R
                    (_, Kind::Loop)
                        if self.is_star(right_id) && left_id == self.get_left(right_id) =>
                    {
                        return left_id;
                    }
                    (Kind::Loop, _) if self.is_star(left_id) => {
                        if right_id == self.get_left(left_id) {
                            return right_id;
                        }
                    }
                    (Kind::Concat, _) if self.get_left(left_id) == NodeId::TOPSTAR => {
                        let concat_tail = self.get_right(left_id);
                        // effectively ends_with
                        if !self.meta_is_infinite(concat_tail) {
                            let rev_left = self.reverse(concat_tail);
                            let rev_left_ts = self.mk_concat(rev_left, NodeId::TOPSTAR);
                            let rev_right = self.reverse(right_id);
                            let rev_inter = self.mk_inter(rev_left_ts, rev_right);
                            // impossible endswith
                            if self.is_empty_lang_cached(rev_inter) {
                                return self.override_key(key, NodeId::BOT);
                            }
                            // subsumed endswith
                            if self.subsumes(rev_left_ts, rev_right) {
                                return self.override_key(key, rev_right);
                            }
                        } else {
                        }
                    }
                    _ => {}
                }
            }
        }
        return self.init(key);
    }

    fn mk_unset(&mut self, kind: Kind) -> NodeId {
        let nullability = match kind {
            Kind::Begin => MetaFlags::BEGIN_NULLABLE,
            Kind::End => MetaFlags::END_NULLABLE,
            // this function is only used to initialize nodes, never called elsewhere
            _ => {
                unreachable!("unset nullability: {:?}", kind)
            }
        };
        let metaid = self.mb.get_meta_id(Metadata { flags: nullability });
        let node = Node {
            kind,
            left: NodeId::MISSING,
            right: NodeId::MISSING,
            extra: u32::MAX,
            meta: metaid,
        };
        self.init(node)
    }

    pub fn mk_loop(&mut self, body_id: NodeId, lower: u32, upper: u32) -> NodeId {
        // _*{500} is _*, ε{500} is ε
        if body_id == NodeId::TOPSTAR || body_id == NodeId::EPS {
            return body_id;
        }
        if lower == 0 && upper == 0 {
            return NodeId::EPS;
        }
        if lower == 1 && upper == 1 {
            return body_id;
        }
        if lower == 0 && upper == 1 {
            return self.mk_union(NodeId::EPS, body_id);
        }
        if lower == 0 {
            match self.get_node(body_id) {
                // removing eps from zero loop (|a)* -> a*
                Node {
                    kind: Kind::Union, ..
                } if self.get_node(body_id).left == NodeId::EPS => {
                    return self.mk_loop(self.get_node(body_id).right, 0, upper);
                }
                _ => {}
            }
        }

        let metaid = self.mb.get_meta_id(Metadata {
            flags: self
                .mb
                .flags_loop(self.get_node_meta_id(body_id), lower, upper),
        });
        let node = Node {
            kind: Kind::Loop,
            left: body_id,
            right: NodeId(lower),
            extra: upper,
            meta: metaid,
        };
        self.get_node_id(node)
    }

    /// it's cheaper to check this once as an edge-case for the empty string
    /// than to compute a 4th nullability bit for every node
    pub fn is_nullable_emptystring(&self, node_id: NodeId) -> Nullability {
        match self.get_node(node_id) {
            Node {
                kind: Kind::Eps, ..
            } => Nullability::ALWAYS,
            Node {
                kind: Kind::End, ..
            } => Nullability::EMPTY_STRING,
            Node {
                kind: Kind::Begin, ..
            } => Nullability::EMPTY_STRING,
            Node {
                kind: Kind::Pred, ..
            } => Nullability::NEVER,
            Node {
                kind: Kind::Loop,
                left: body,
                right: lower,
                ..
            } => {
                if lower.0 == 0 {
                    Nullability::ALWAYS
                } else {
                    self.is_nullable_emptystring(*body)
                }
            }
            Node {
                kind: Kind::Concat, ..
            } => {
                let lnull = self.is_nullable_emptystring(self.get_left(node_id));
                let rnull = self.is_nullable_emptystring(self.get_right(node_id));
                lnull & rnull // left = 010, right = 001, left & right = 000
            }
            Node {
                kind: Kind::Union, ..
            } => {
                let lnull = self.is_nullable_emptystring(self.get_left(node_id));
                let rnull = self.is_nullable_emptystring(self.get_right(node_id));
                lnull | rnull
            }
            Node {
                kind: Kind::Inter, ..
            } => {
                let lnull = self.is_nullable_emptystring(self.get_left(node_id));
                let rnull = self.is_nullable_emptystring(self.get_right(node_id));
                lnull & rnull
            }
            Node {
                kind: Kind::Compl, ..
            } => !self.is_nullable_emptystring(self.get_left(node_id)),
            Node {
                kind: Kind::Lookaround,
                ..
            } => {
                let lb = if self.get_left(node_id) == NodeId::MISSING {
                    Nullability::ALWAYS
                } else {
                    self.is_nullable_emptystring(self.get_left(node_id))
                };
                let la = if self.get_right(node_id) == NodeId::MISSING {
                    Nullability::ALWAYS
                } else {
                    self.is_nullable_emptystring(self.get_right(node_id))
                };
                lb & la & self.is_nullable_emptystring(NodeId(self.get_node(node_id).extra))
            }
            Node {
                kind: Kind::Lookbehind,
                ..
            } => self.is_nullable_emptystring(self.get_left(node_id)),
            Node {
                kind: Kind::Lookahead,
                ..
            } => self.is_nullable_emptystring(self.get_left(node_id)),
        }
    }

    #[inline(always)]
    pub fn any_nonbegin_nullable(&self, node_id: NodeId) -> bool {
        self.get_meta(node_id).flags.any_nonbegin_null()
    }
    #[inline(always)]
    pub fn nullability(&self, node_id: NodeId) -> Nullability {
        self.get_meta_nullability(node_id)
    }

    /// pretty-print to string
    pub fn pp(&self, node_id: NodeId) -> String {
        let mut s = String::new();
        self.ppw(&mut s, node_id).unwrap();
        s
    }

    /// pretty-print transition regex
    pub fn ppt(&self, term_id: TRegexId) -> String {
        match self.get_tregex(term_id) {
            TRegex::Leaf(node_id) => {
                let mut s = String::new();
                self.ppw(&mut s, *node_id).unwrap();
                s
            }
            TRegex::ITE(cond, then_id, else_id) => {
                format!(
                    "ITE({},{},{})",
                    self.mb.solver.pp(*cond),
                    self.ppt(*then_id),
                    self.ppt(*else_id)
                )
            }
        }
    }

    /// pretty-print to writer
    fn ppw(&self, s: &mut String, node_id: NodeId) -> Result<(), std::fmt::Error> {
        match node_id {
            NodeId::MISSING => return write!(s, "MISSING"),
            NodeId::BOT => return write!(s, "⊥"),
            NodeId::TOPSTAR => return write!(s, "_*"),
            NodeId::TOP => return write!(s, "_"),
            NodeId::EPS => return write!(s, "ε"),
            _ => {}
        }

        match self.get_node(node_id) {
            Node {
                kind: Kind::Eps,
                extra: 0,
                ..
            } => return write!(s, "ε"),
            Node {
                kind: Kind::Eps,
                extra: e,
                ..
            } => return write!(s, "ε{{{e}}}"),
            Node {
                kind: Kind::End, ..
            } => return write!(s, r"\z"),
            Node {
                kind: Kind::Begin, ..
            } => return write!(s, r"\A"),
            Node {
                kind: Kind::Pred, ..
            } => {
                let psi = self.get_pred_tset(node_id);
                if self.mb.solver.is_empty_id(psi) {
                    return write!(s, r"⊥");
                } else if self.mb.solver.is_full_id(psi) {
                    return write!(s, r"_");
                } else {
                    return write!(s, "{}", self.mb.solver.pp(psi));
                }
            }
            Node {
                kind: Kind::Inter,
                left,
                right,
                ..
            } => {
                write!(s, "(")?;
                self.ppw(s, *left)?;
                write!(s, "&")?;
                let mut curr = *right;
                while self.get_kind(curr) == Kind::Inter {
                    let n = self.get_left(curr);
                    self.ppw(s, n)?;
                    write!(s, "&")?;
                    curr = self.get_right(curr);
                }
                self.ppw(s, curr)?;
                write!(s, ")")
            }
            Node {
                kind: Kind::Union,
                left,
                right,
                ..
            } => {
                write!(s, "(")?;
                self.ppw(s, *left)?;
                write!(s, "|")?;
                let mut curr = *right;
                while self.get_kind(curr) == Kind::Union {
                    let n = self.get_left(curr);
                    self.ppw(s, n)?;
                    write!(s, "|")?;
                    curr = self.get_right(curr);
                }
                self.ppw(s, curr)?;
                write!(s, ")")
            }
            Node {
                kind: Kind::Concat,
                left,
                right,
                ..
            } => {
                self.ppw(s, *left)?;
                self.ppw(s, *right)
            }
            Node {
                kind: Kind::Loop,
                left,
                right: lower,
                extra: upper,
                ..
            } => {
                let leftkind = self.get_node_kind(*left);
                match leftkind {
                    Kind::Concat | Kind::Loop | Kind::Lookaround | Kind::Compl => {
                        write!(s, "(")?;
                        self.ppw(s, *left)?;
                        write!(s, ")")?;
                    }
                    _ => {
                        self.ppw(s, *left)?;
                    }
                };
                if *upper == u32::MAX && lower.0 == 0 {
                    write!(s, "*")
                } else if *upper == u32::MAX && lower.0 == 1 {
                    write!(s, "+")
                } else if *upper == 1 && lower.0 == 0 {
                    write!(s, "?")
                } else if *upper == lower.0 {
                    write!(s, "{{{}}}", upper)
                } else if *upper == u32::MAX {
                    write!(s, "{{{},}}", lower.0)
                } else {
                    write!(s, "{{{},{}}}", lower.0, upper)
                }
            }
            Node {
                kind: Kind::Compl,
                left,
                ..
            } => {
                write!(s, "~(")?;
                self.ppw(s, *left)?;
                write!(s, ")")
            }
            Node {
                kind: Kind::Lookbehind,
                left: lookbehind,
                ..
            } => {
                write!(s, "(?<=")?;
                self.ppw(s, *lookbehind)?;
                write!(s, ")")
            }
            Node {
                kind: Kind::Lookahead,
                left: lookahead,
                ..
            } => {
                write!(s, "(?=")?;
                self.ppw(s, *lookahead)?;
                write!(s, ")")
            }
            Node {
                kind: Kind::Lookaround,
                left: lookbehind,
                right: lookahead,
                extra: body,
                ..
            } => {
                if *lookbehind == NodeId::MISSING {
                } else {
                    self.ppw(s, *lookbehind)?;
                };

                self.ppw(s, NodeId(*body))?;
                if *lookahead == NodeId::MISSING {
                    Ok(())
                } else {
                    self.ppw(s, *lookahead)
                }
            }
        }
    }

    pub fn mk_pred_not(&mut self, set: TSetId) -> NodeId {
        let not_pred = self.solver().not_id(set);
        self.mk_pred(not_pred)
    }

    pub fn mk_u8(&mut self, char: u8) -> NodeId {
        let pred = self.solver().u8_to_set_id(char);
        self.mk_pred(pred)
    }

    pub fn mk_range_u8(&mut self, start: u8, end_inclusive: u8) -> NodeId {
        let pred = self.solver().range_to_set_id(start, end_inclusive);
        self.mk_pred(pred)
    }

    pub fn mk_bytestring(&mut self, raw_str: &[u8]) -> NodeId {
        let mut result = NodeId::EPS;
        for byte in raw_str.into_iter().rev() {
            let node = self.mk_u8(*byte);
            result = self.mk_concat(node, result);
        }
        result
    }

    pub fn mk_string(&mut self, raw_str: &str) -> NodeId {
        let mut result = NodeId::EPS;
        // iterate string bytes
        for byte in raw_str.bytes().rev() {
            let node = self.mk_u8(byte);
            result = self.mk_concat(node, result);
        }
        result
    }

    pub fn mk_unions(&mut self, nodes: impl Iterator<Item = NodeId>) -> NodeId {
        let mut vec = nodes.collect::<Vec<NodeId>>();
        vec.sort();
        vec.iter()
            .rev()
            .fold(NodeId::BOT, |acc, x| self.mk_union(*x, acc))
    }

    pub fn mk_unions_set(&mut self, nodes: BTreeSet<NodeId>) -> NodeId {
        nodes
            .iter()
            .rev()
            .fold(NodeId::BOT, |acc, x| self.mk_union(*x, acc))
    }

    pub fn mk_inters(&mut self, mut nodes: Vec<NodeId>) -> NodeId {
        let mut result = NodeId::TOPSTAR;
        nodes.sort();
        nodes.iter().rev().for_each(|node| {
            result = self.mk_inter(*node, result);
        });
        result
    }

    pub fn mk_concats(&mut self, nodes: impl DoubleEndedIterator<Item = NodeId>) -> NodeId {
        nodes
            .rev()
            .fold(NodeId::EPS, |acc, x| self.mk_concat(x, acc))
    }

    pub fn mk_concats_slice(&mut self, nodes: &[NodeId]) -> NodeId {
        nodes
            .iter()
            .rev()
            .fold(NodeId::EPS, |acc, x| self.mk_concat(*x, acc))
    }
}

impl RegexBuilder {
    pub fn extract_sat(&self, tregex_id: TRegexId) -> Vec<NodeId> {
        match *self.get_tregex(tregex_id) {
            TRegex::Leaf(node_id) => {
                if NodeId::BOT == node_id {
                    vec![]
                } else {
                    vec![node_id]
                }
            }
            TRegex::ITE(cond, then_id, else_id) => {
                if self.mb.solver.is_empty_id(cond) {
                    return self.extract_sat(else_id);
                }
                let mut then_nodes = self.extract_sat(then_id);
                let mut else_nodes = self.extract_sat(else_id);
                then_nodes.append(&mut else_nodes);
                then_nodes
            }
        }
    }

    pub fn iter_find_stack(
        &self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(NodeId) -> bool,
    ) -> bool {
        loop {
            match stack.pop() {
                None => return false,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        let mut curr = n;
                        while curr != NodeId::BOT {
                            match self.get_kind(curr) {
                                Kind::Union => {
                                    if f(self.get_left(curr)) {
                                        return true;
                                    }
                                    curr = self.get_right(curr);
                                }
                                _ => {
                                    if f(n) {
                                        return true;
                                    }
                                    curr = NodeId::BOT;
                                }
                            }
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(then_id);
                        if else_id != TRegexId::BOT {
                            stack.push(else_id);
                        }
                    }
                },
            }
        }
    }

    pub fn iter_find_stack_non_null(
        &self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(NodeId) -> bool,
    ) -> bool {
        loop {
            match stack.pop() {
                None => return false,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        if f(n) {
                            return true;
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(else_id);
                        stack.push(then_id);
                    }
                },
            }
        }
    }

    pub fn iter_find_stack_counterexample(
        &self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(NodeId) -> Option<NodeId>,
    ) -> Option<NodeId> {
        loop {
            match stack.pop() {
                None => return None,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        let mut curr = n;
                        while curr != NodeId::BOT {
                            match self.get_kind(curr) {
                                Kind::Union => {
                                    if let Some(v) = f(self.get_left(curr)) {
                                        return Some(v);
                                    }
                                    curr = self.get_right(curr);
                                }
                                _ => {
                                    if let Some(v) = f(n) {
                                        return Some(v);
                                    }
                                    curr = NodeId::BOT;
                                }
                            }
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(then_id);
                        if else_id != TRegexId::BOT {
                            stack.push(else_id);
                        }
                    }
                },
            }
        }
    }

    // for existence of a match concat is equivalent to lookarounds:
    // IsNonempty((?<=𝐿 1 )·𝐿 2 ·(?=𝐿 3 )) = IsNonempty(_*·𝐿 1 ·𝐿 2 ·𝐿 3 ·_*)
    pub fn elim_lookarounds_ismatch(&mut self, node_id: NodeId) -> NodeId {
        if !self.meta_contains_lookaround(node_id) {
            return node_id;
        }
        match self.get_kind(node_id) {
            Kind::Compl => {
                let left = self.get_left(node_id);
                let elim_l = self.elim_lookarounds_ismatch(left);
                self.mk_compl(elim_l)
            }
            Kind::Eps => return NodeId::EPS,
            Kind::Pred | Kind::Begin | Kind::End => return node_id,
            Kind::Concat => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                let elim_l = self.elim_lookarounds_ismatch(left);
                let elim_r = self.elim_lookarounds_ismatch(right);
                let rw = self.mk_concat(elim_l, elim_r);
                rw
            }
            Kind::Union => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                let elim_l = self.elim_lookarounds_ismatch(left);
                let elim_r = self.elim_lookarounds_ismatch(right);
                let rw = self.mk_union(elim_l, elim_r);
                rw
            }

            Kind::Loop => {
                let body = self.get_left(node_id);
                let elim_l = self.elim_lookarounds_ismatch(body);
                self.mk_loop(elim_l, self.get_right(node_id).0, self.get_extra(node_id))
            }
            Kind::Lookaround => {
                let lookbehind = match self.get_left(node_id) {
                    NodeId::MISSING => NodeId::TOPSTAR,
                    lb => self.get_left(lb),
                };
                let lookahead = match self.get_right(node_id) {
                    NodeId::MISSING => NodeId::TOPSTAR,
                    la => self.get_left(la),
                };
                let body = NodeId(self.get_extra(node_id));
                let elim_lb = self.elim_lookarounds_ismatch(lookbehind);
                let elim_body = self.elim_lookarounds_ismatch(body);
                let elim_la = self.elim_lookarounds_ismatch(lookahead);
                self.mk_concats(
                    [
                        NodeId::TOPSTAR,
                        elim_lb,
                        elim_body,
                        elim_la,
                        NodeId::TOPSTAR,
                    ]
                    .into_iter(),
                )
            }
            Kind::Lookbehind => unreachable!(),
            Kind::Lookahead => unreachable!(),
            Kind::Inter => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                let elim_l = self.elim_lookarounds_ismatch(left);
                let elim_r = self.elim_lookarounds_ismatch(right);
                let rw = self.mk_inter(elim_l, elim_r);
                rw
            }
        }
    }

    pub fn is_empty_lang_cached(&mut self, node: NodeId) -> bool {
        if node == NodeId::BOT {
            return true;
        }
        if self.nullability(node) != Nullability::NEVER {
            return false;
        }
        if let Some(cached) = self.cache_empty.get(&node) {
            if cached.is_checked() {
                return cached.is_empty();
            }
        }
        let strip_node = self.elim_lookarounds_ismatch(node);
        let isempty_flag = self.is_empty_lang(strip_node);
        self.cache_empty
            .insert(node, NodeFlags(isempty_flag.0 | NodeFlags::CHECKED_EMPTY.0));
        isempty_flag == NodeFlags::IS_EMPTY
    }

    pub fn is_empty_lang(&mut self, node: NodeId) -> NodeFlags {
        if node == NodeId::BOT {
            return NodeFlags::IS_EMPTY;
        }

        // check trivial cases,
        // without inter, no need to check, complement is checked during construction
        if self.nullability(node) != Nullability::NEVER
            || !self.get_meta_flags(node).contains_inter()
        {
            return NodeFlags::ZERO;
        }

        // unique nodes that have been visited
        let mut visited: HashSet<NodeId> = HashSet::new();
        let mut todo: VecDeque<NodeId> = VecDeque::new();
        visited.insert(NodeId::BOT);

        // insert beginning derivatives
        // if anchors are not important then this part can be removed completely
        let begin_der = self.der(node, Nullability::BEGIN);
        let begin_nodes = self.extract_sat(begin_der);
        for node in begin_nodes {
            visited.insert(node);
            if self.nullability(node) != Nullability::NEVER {
                return NodeFlags::ZERO;
            }
            todo.push_back(node);
        }

        todo.push_back(node);
        let mut stack = Vec::new();
        let mut num_of_derivatives_taken = 0;

        loop {
            match todo.pop_front() {
                None => {
                    return NodeFlags::IS_EMPTY;
                }
                Some(node) => {
                    let derivative = self.der(node, Nullability::CENTER);
                    stack.push(derivative);
                    let found_null = self.iter_find_stack(&mut stack, |node| {
                        if visited.contains(&node) {
                            return false;
                        }
                        if let Some(cached) = self.cache_empty.get(&node) {
                            if cached.is_checked() {
                                if cached.is_empty() {
                                    return false;
                                } else {
                                    return true;
                                }
                            }
                        }

                        // this is a good way to determine if performance improved or not
                        if cfg!(feature = "count_derivatives") {
                            num_of_derivatives_taken += 1;
                            println!("num of ders:{num_of_derivatives_taken:?}");
                            // println!("der: {:?}", self.ppt(derivative));
                        }

                        if !self.get_meta_flags(node).contains_inter() {
                            // this node is inferred to be satisfiable
                            // we can stop here unless we need an example input string
                            return true;
                        } else {
                            visited.insert(node);
                            todo.push_front(node);

                            // if this node is nullable, then you can
                            // produce a valid input string for this regex from
                            // any path that reaches this node.
                            self.any_nonbegin_nullable(node)
                        }
                    });
                    if found_null {
                        return NodeFlags::ZERO;
                    }
                }
            }
        }
    }

    /// compares language to \_\*, used to turn ~(\_\*) to ⊥
    pub fn is_full_lang(&mut self, node: NodeId) -> bool {
        if node == NodeId::TOPSTAR {
            return true;
        }
        // check trivial cases,
        if node == NodeId::EPS || self.nullability(node) == Nullability::NEVER {
            return false;
        }

        // unique nodes that have been visited
        let mut visited: HashSet<NodeId> = HashSet::new();
        let mut todo: VecDeque<NodeId> = VecDeque::new();
        // insert beginning derivatives
        let begin_der = self.der(node, Nullability::BEGIN);
        let begin_nodes = self.extract_sat(begin_der);
        for node in begin_nodes {
            visited.insert(node);
            if self.nullability(node) != Nullability::ALWAYS {
                return false;
            }
            todo.push_back(node);
        }

        todo.push_back(node);
        let mut stack = Vec::new();
        let mut num_of_derivatives_taken = 0;

        loop {
            match todo.pop_front() {
                None => {
                    // is full lang
                    return true;
                }
                Some(node) => {
                    let derivative = self.der(node, Nullability::CENTER);
                    stack.push(derivative);
                    let found_non_null = self.iter_find_stack_non_null(&mut stack, |node| {
                        if visited.contains(&node) {
                            return false;
                        }
                        // this is a good way to determine if performance improved or not
                        if cfg!(feature = "count_derivatives") {
                            num_of_derivatives_taken += 1;
                            println!("num of ders (full):{num_of_derivatives_taken:?}");
                            println!("der: {:?}", self.ppt(derivative));
                        }

                        visited.insert(node);
                        todo.push_front(node);
                        self.nullability(node) == Nullability::NEVER
                    });
                    if found_non_null {
                        return false;
                    }
                }
            }
        }
    }

    pub fn is_equiv(&mut self, nodea: NodeId, nodeb: NodeId) -> bool {
        // equiv = A⊕B = (A\B)∪(B\A) = ⊥
        let nota = self.mk_compl(nodea);
        let notb = self.mk_compl(nodeb);
        let anotb = self.mk_inter(nodea, notb);
        let bnota = self.mk_inter(nodeb, nota);
        let diff = self.mk_union(anotb, bnota);
        self.is_empty_lang_cached(diff)
    }

    fn wrap_in_ts(&mut self, node: NodeId) -> NodeId {
        let tmp = self.mk_concat(node, NodeId::TOPSTAR);
        self.mk_concat(NodeId::TOPSTAR, tmp)
    }

    pub fn subsumes(&mut self, larger_lang: NodeId, smaller_lang: NodeId) -> bool {
        // short-circuit
        if larger_lang == smaller_lang {
            return true;
        }
        // assess initial nullability
        let null_small = self.nullability(smaller_lang);
        if self.nullability(larger_lang).0 & null_small.0 != null_small.0 {
            return false;
        }

        let (smaller_lang, larger_lang) =
            if self.contains_look(smaller_lang) || self.contains_look(larger_lang) {
                (self.wrap_in_ts(smaller_lang), self.wrap_in_ts(larger_lang))
            } else {
                (smaller_lang, larger_lang)
            };
        // check language nullability
        // if (B &~ A) ≡ ⊥ then B ⊆ A
        let nota = self.mk_compl(larger_lang);
        let diff = self.mk_inter(smaller_lang, nota);
        let is_empty = self.is_empty_lang_cached(diff);

        is_empty
    }

    /// this returns the found satisfiable node id.
    /// any path from the start state to this node id is a valid string prefix for a match.
    /// for a complete string the returned node id must be explored till nullability
    pub fn is_empty_lang_w_counterexample(&mut self, node: NodeId) -> Option<NodeId> {
        if node == NodeId::BOT {
            return None;
        }

        // check trivial cases,
        // without inter, no need to check, complement is checked during construction
        if self.nullability(node) != Nullability::NEVER
            || !self.get_meta_flags(node).contains_inter()
        {
            return Some(node);
        }
        let node = self.elim_lookarounds_ismatch(node);

        // unique nodes that have been visited
        let mut visited: HashSet<NodeId> = HashSet::new();
        let mut todo: VecDeque<NodeId> = VecDeque::new();
        visited.insert(NodeId::BOT);
        // insert beginning derivatives
        let begin_der = self.der(node, Nullability::BEGIN);
        let begin_nodes = self.extract_sat(begin_der);
        for node in begin_nodes {
            visited.insert(node);
            if self.nullability(node) != Nullability::NEVER {
                return Some(node);
            }
            todo.push_back(node);
        }

        todo.push_back(node);
        let mut stack = Vec::new();

        loop {
            match todo.pop_front() {
                None => {
                    return None;
                }
                Some(node) => {
                    let derivative = self.der(node, Nullability::CENTER);
                    stack.push(derivative);
                    let found_null = self.iter_find_stack_counterexample(&mut stack, |node| {
                        if visited.contains(&node) {
                            return None;
                        }
                        if let Some(cached) = self.cache_empty.get(&node) {
                            if cached.is_checked() {
                                if cached.is_empty() {
                                    return None;
                                } else {
                                    return Some(node);
                                }
                            }
                        }

                        if !self.get_meta_flags(node).contains_inter() {
                            return Some(node);
                        } else {
                            visited.insert(node);
                            todo.push_front(node);

                            if self.any_nonbegin_nullable(node) {
                                Some(node)
                            } else {
                                None
                            }
                        }
                    });
                    if let Some(v) = found_null {
                        return Some(v);
                    }
                }
            }
        }
    }
}
