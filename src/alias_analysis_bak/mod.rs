use std::collections::{BTreeMap, LinkedList};
#[derive(Default, PartialEq, Eq, PartialOrd, Ord)]
struct Value(u32);
#[derive(Default, PartialEq, Eq, PartialOrd, Ord)]
struct MemoryLocation(u32);
#[derive(Default, PartialEq, Eq, PartialOrd, Ord)]
struct AAResult(u32);
#[derive(Default, PartialEq, Eq, PartialOrd, Ord)]
struct CallBase(u32);

#[derive(Default, PartialEq, Eq, PartialOrd, Ord)]
struct AnalysisKey(u32);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum AliasResult {
    NoAlias = 0,
    MayAlias,
    PartialAlias,
    MustAlias,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
struct ModRefInfo(u8);
impl ModRefInfo {
    pub const Must: u8 = 0;
    pub const MustRef: u8 = 1;
    pub const MustMod: u8 = 2;
    pub const MustModRef: u8 = ModRefInfo::MustRef | ModRefInfo::MustMod;
    pub const NoModRef: u8 = 4;
    pub const Ref: u8 = ModRefInfo::NoModRef | ModRefInfo::MustRef;
    pub const Mod: u8 = ModRefInfo::NoModRef | ModRefInfo::MustMod;
    pub const ModRef: u8 = ModRefInfo::Ref | ModRefInfo::Mod;
}

struct CacheEntry {
    result: AliasResult,
    num_assumption_uses: i32,
}

impl CacheEntry {
    const fn is_definitive(&self) -> bool { 
        self.num_assumption_uses < 0
    }
}

type LocPair = (MemoryLocation, MemoryLocation);
type AliasCacheT = BTreeMap<LocPair, CacheEntry>;
type IsCapturedCacheT = BTreeMap<Value, bool>;
#[derive(Default)]
struct AAQueryInfo {
    alias_cache: AliasCacheT,
    is_captured_cache: IsCapturedCacheT,
}

struct AAResults {
    aas: Vec<AAResult>,
    aa_deps: Vec<AnalysisKey>,
}

impl AAResults {
    pub fn new() -> Self {
        todo!{}
    }
    pub fn add_aa_result(&mut self, aa_result: AAResult) {
        self.aas.push(aa_result);
    }
    pub fn add_aa_dependency_id(&mut self, id: AnalysisKey) {
        self.aa_deps.push(id);
    }
    // pub fn invalid(...)
    pub fn alias(&self, lhs: &MemoryLocation, rhs: &MemoryLocation) -> AliasResult {
        AliasResult::MayAlias
    }
}

struct PointerRec {
    value: Value,
    alias_set: Option<AliasSet>,
}

impl PointerRec {
    pub fn value(&self) -> &Value {
        &self.value
    }
    pub fn has_alias_set(&self) -> bool {
        match self.alias_set {
            Some(_) => true,
            None => false,
        }
    }
    pub fn get_alias_set(&mut self, ast: &mut AliasSetTracker) -> Option<&AliasSet> {
        if let Some(ref mut alias_set) = self.alias_set {
            // if alias_set.forward.is_some() {
            //     let old = alias_set;
            //     self.alias_set = old.get_forwarded_target(ast);
            //     self.alias_set.add_ref();
            //     old.drop_ref(ast);
            // }
            Some(alias_set)
        } else {
            None
        }
    }

    pub fn set_alias_set(&mut self, alias_set: AliasSet) -> Result<(), &str> {
        match self.alias_set {
            Some(_) => Err("Already have an alias set!"),
            None => {
                self.alias_set = Some(alias_set);
                Ok(())
            }
        }
    }
}


#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
struct AccessLattice;
impl AccessLattice {
    pub const NoAccess: u8 = 0;
    pub const RefAccess: u8 = 1;
    pub const ModAccess: u8 = 2;
    pub const ModRefAccess: u8 = AccessLattice::RefAccess | AccessLattice::ModAccess;
}

#[repr(u8)]
enum AliasLattice {
    SetMustAlias = 0,
    SetMayAlias = 1,
}

// LinkedList<Node>
struct AliasSet {
    ptr_list: LinkedList<PointerRec>,
    forward: Option<*mut AliasSet>,
    // unknown_insts: Vec<WeakVH>,
    ref_count: u32, // u27
    alias_any: bool,
    access: u16,
    alias: bool,
    set_size: u32,
}

impl AliasSet {
    fn add_ref(&mut self) {
        self.ref_count += 1;
    }

    fn drop_ref(ast: &mut AliasSetTracker) {

    }
}



struct AliasSetTracker {
    aa: AAResults
}

struct BasicAAResult {

}

impl BasicAAResult {
    pub fn new(/*f: &Function*/) -> BasicAAResult {
        BasicAAResult {}
    }

    // copy, move ctor
    pub fn invalid(&self/*f: &Function*/) -> bool {
        false
    }

    pub fn alias(lhs: &MemoryLocation, rhs: &MemoryLocation, aaqi: &AAQueryInfo) -> AliasResult {
        AliasResult::MayAlias
    }

    pub fn get_mod_ref_info(call: &CallBase, loc: &MemoryLocation, aaqi: &AAQueryInfo) -> ModRefInfo {
        ModRefInfo(ModRefInfo::ModRef)
    }

    pub fn get_mod_ref_info_call(call1: &CallBase, call2: &CallBase, aaqi: &AAQueryInfo) -> ModRefInfo {
        ModRefInfo(ModRefInfo::ModRef)
    }

    pub fn points_to_constant_memory(loc: &MemoryLocation, aaqi: &AAQueryInfo, or_local: bool) -> bool {
        false
    }
}