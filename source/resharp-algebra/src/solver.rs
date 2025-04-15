type TSet = std::simd::u64x4; // 256-bit vector

const EMPTY: &'static [u64; 4] = &[u64::MIN, u64::MIN, u64::MIN, u64::MIN];
const FULL: &'static [u64; 4] = &[u64::MAX, u64::MAX, u64::MAX, u64::MAX];

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
pub struct TSetId(pub u32);
impl TSetId {
    pub const EMPTY: TSetId = TSetId(0);
    pub const FULL: TSetId = TSetId(1);
}

use std::{
    collections::{BTreeMap, BTreeSet},
    mem,
};

pub struct Solver {
    // hashing is more expensive here than btree
    cache: BTreeMap<TSet, TSetId>,
    pub array: Vec<TSet>,
}

impl Solver {
    pub fn new() -> Solver {
        let mut inst = Self {
            cache: BTreeMap::new(),
            array: Vec::new(),
        };
        let _ = inst.init(Solver::empty());
        let _ = inst.init(Solver::full());
        inst
    }

    fn init(&mut self, inst: TSet) -> TSetId {
        let new_id = TSetId(self.cache.len() as u32);
        self.cache.insert(inst, new_id);
        self.array.push(inst);
        new_id
    }

    #[inline(always)]
    pub fn get_set(&self, set_id: TSetId) -> TSet {
        self.array[set_id.0 as usize]
    }

    #[inline(always)]
    pub fn get_id(&mut self, inst: TSet) -> TSetId {
        match self.cache.get(&inst) {
            Some(&id) => id,
            None => self.init(inst),
        }
    }

    fn pp_collect_ranges(tset: &TSet) -> BTreeSet<(u8, u8)> {
        let mut ranges: BTreeSet<(u8, u8)> = BTreeSet::new();
        let mut rangestart: Option<u8> = None;
        let mut prevchar: Option<u8> = None;
        for i in 0..4 {
            for j in 0..64 {
                let nthbit = 1u64 << j;
                if tset[i] & nthbit != 0 {
                    let cc = (i * 64 + j) as u8;
                    if rangestart.is_none() {
                        rangestart = Some(cc);
                        prevchar = Some(cc);
                        continue;
                    }

                    if let Some(currstart) = rangestart {
                        if let Some(currprev) = prevchar {
                            if currprev as u8 == cc as u8 - 1 {
                                prevchar = Some(cc);
                                continue;
                            } else {
                                if currstart == currprev {
                                    ranges.insert((currstart, currstart));
                                } else {
                                    ranges.insert((currstart, currprev));
                                }
                                rangestart = Some(cc);
                                prevchar = Some(cc);
                            }
                        } else {
                        }
                    } else {
                    }
                }
            }
        }
        if let Some(start) = rangestart {
            if let Some(prevchar) = prevchar {
                if prevchar as u8 == start as u8 {
                    ranges.insert((start, start));
                } else {
                    ranges.insert((start, prevchar));
                }
            } else {
                // single char
                ranges.insert((start, start));
            }
        }
        ranges
    }

    fn pp_byte(b: u8) -> String {
        match b as char {
            '\n' => r"\n".to_owned(),
            '"' => "\"".to_owned(),
            '\r' => r"\r".to_owned(),
            '\t' => r"\t".to_owned(),
            ' ' => r" ".to_owned(),
            '_' | '.' | '+' | '-' | '\\' | '&' | '|' | '~' | '{' | '}' | '[' | ']' | '(' | ')' => {
                r"\".to_owned() + &(b as char).to_string()
            }
            c if c.is_ascii_punctuation() || c.is_ascii_alphanumeric() => c.to_string(),
            _ => format!("\\x{:02X}", b),
        }
    }

    fn pp_content(ranges: &BTreeSet<(u8, u8)>) -> String {
        let display_range = |c, c2| {
            if c == c2 {
                Self::pp_byte(c)
            } else if c.abs_diff(c2) == 1 {
                format!("{}{}", Self::pp_byte(c), Self::pp_byte(c2))
            } else {
                format!("{}-{}", Self::pp_byte(c), Self::pp_byte(c2))
            }
        };

        if ranges.len() == 0 {
            return "⊥".to_owned();
        }
        if ranges.len() == 1 {
            let (s, e) = ranges.iter().next().unwrap();
            if s == e {
                return Self::pp_byte(*s);
            } else {
                return format!(
                    "{}",
                    ranges
                        .iter()
                        .map(|(s, e)| display_range(*s, *e))
                        .collect::<Vec<_>>()
                        .join("")
                );
            }
        }
        if ranges.len() > 20 {
            return "φ".to_owned();
        }
        return format!(
            "{}",
            ranges
                .iter()
                .map(|(s, e)| display_range(*s, *e))
                .collect::<Vec<_>>()
                .join("")
        );
    }

    pub fn pp(&self, tset: TSetId) -> String {
        if tset == TSetId::FULL {
            return "_".to_owned();
        }
        if tset == TSetId::EMPTY {
            return "⊥".to_owned();
        }
        let tset = self.get_set(tset);
        let ranges: BTreeSet<(u8, u8)> = Self::pp_collect_ranges(&tset);
        let rstart = ranges.first().unwrap().0;
        let rend = ranges.last().unwrap().1;
        if ranges.len() >= 2 && rstart == 0 && rend == 255 {
            let not_id = Self::not(&tset);
            let not_ranges = Self::pp_collect_ranges(&not_id);
            if not_ranges.len() == 1 && not_ranges.iter().next() == Some(&(10, 10)) {
                return r".".to_owned();
            }
            let content = Self::pp_content(&not_ranges);
            return format!("[^{}]", content);
        }
        if ranges.len() == 0 {
            return "⊥".to_owned();
        }
        if ranges.len() == 1 {
            let (s, e) = ranges.iter().next().unwrap();
            if s == e {
                return Self::pp_byte(*s);
            } else {
                let content = Self::pp_content(&ranges);
                return format!("[{}]", content);
            }
        }
        let content = Self::pp_content(&ranges);
        return format!("[{}]", content);
    }
}

impl Solver {
    #[inline]
    pub fn full() -> TSet {
        unsafe { mem::transmute::<[u64; 4], TSet>(*FULL) }
    }

    #[inline]
    pub fn empty() -> TSet {
        unsafe { mem::transmute::<[u64; 4], TSet>(*EMPTY) }
    }

    #[inline]
    pub fn or_id(&mut self, set1: TSetId, set2: TSetId) -> TSetId {
        if set1 == TSetId::FULL || set2 == TSetId::FULL {
            return TSetId::FULL;
        }
        if set1 == TSetId::EMPTY {
            return set2;
        }
        if set2 == TSetId::EMPTY {
            return set1;
        }
        let res = self.get_set(set1) | self.get_set(set2);
        self.get_id(res)
    }

    #[inline]
    pub fn and_id(&mut self, set1: TSetId, set2: TSetId) -> TSetId {
        if set1 == TSetId::EMPTY || set2 == TSetId::EMPTY {
            return TSetId::EMPTY;
        }
        if set1 == TSetId::FULL {
            return set2;
        }
        if set2 == TSetId::FULL {
            return set1;
        }
        self.get_id(self.get_set(set1) & self.get_set(set2))
    }

    #[inline]
    pub fn not_id(&mut self, set_id: TSetId) -> TSetId {
        if set_id == TSetId::EMPTY {
            TSetId::FULL
        } else if set_id == TSetId::FULL {
            TSetId::EMPTY
        } else {
            let res = self.get_set(set_id);
            self.get_id(!(res))
        }
    }

    #[inline]
    pub fn is_sat_id(&mut self, set1: TSetId, set2: TSetId) -> bool {
        self.and_id(set1, set2) != TSetId::EMPTY
    }
    #[inline]
    pub fn unsat_id(&mut self, set1: TSetId, set2: TSetId) -> bool {
        self.and_id(set1, set2) == TSetId::EMPTY
    }

    #[inline]
    pub fn is_empty_id(&self, set1: TSetId) -> bool {
        set1 == TSetId::EMPTY
    }

    #[inline]
    pub fn is_full_id(&self, set1: TSetId) -> bool {
        set1 == TSetId::FULL
    }

    #[inline]
    pub fn contains_id(&mut self, large_id: TSetId, small_id: TSetId) -> bool {
        let not_large = self.not_id(large_id);
        self.and_id(small_id, not_large) == TSetId::EMPTY
    }

    pub fn u8_to_set_id(&mut self, byte: u8) -> TSetId {
        let mut result = TSet::splat(u64::MIN);
        let nthbit = 1u64 << byte % 64;
        match byte {
            0..=63 => {
                result[0] = nthbit;
            }
            64..=127 => {
                result[1] = nthbit;
            }
            128..=191 => {
                result[2] = nthbit;
            }
            192..=255 => {
                result[3] = nthbit;
            }
        }
        self.get_id(result)
    }

    pub fn range_to_set_id(&mut self, start: u8, end: u8) -> TSetId {
        let mut result = TSet::splat(u64::MIN);
        for byte in start..=end {
            let nthbit = 1u64 << byte % 64;
            match byte {
                0..=63 => {
                    result[0] |= nthbit;
                }
                64..=127 => {
                    result[1] |= nthbit;
                }
                128..=191 => {
                    result[2] |= nthbit;
                }
                192..=255 => {
                    result[3] |= nthbit;
                }
            }
        }
        self.get_id(result)
    }

    #[inline]
    pub fn and(set1: &TSet, set2: &TSet) -> TSet {
        set1 & set2
    }

    #[inline]
    pub fn is_sat(set1: &TSet, set2: &TSet) -> bool {
        set1 & set2 != Solver::empty()
    }

    #[inline]
    pub fn or(set1: &TSet, set2: &TSet) -> TSet {
        set1 | set2
    }

    #[inline]
    pub fn not(set: &TSet) -> TSet {
        !(*set)
    }

    #[inline]
    pub fn is_full(set: &TSet) -> bool {
        *set == Self::full()
    }

    #[inline]
    pub fn is_empty(set: &TSet) -> bool {
        *set == Solver::empty()
    }

    #[inline]
    pub fn contains(large: &TSet, small: &TSet) -> bool {
        Solver::empty() == (small & !(*large))
    }
}
