//! The built-in registry (docs/proposals/namespaces.md §4.7): the prelude
//! declarations that syntax, natives, the effect machinery, extraction, the
//! printer and the runner mean, by identity rather than by name.
//!
//! `a + b` means the prelude's `add`, whatever `add` means where it's
//! written; a user's own `List` never gets the list codec. Its invariants:
//!
//! 1. Each entry is a final declaration of these [`Globals`], so ids are
//!    never carried between environments.
//! 2. Only loading the prelude binds entries ([`bind_data`], [`bind_def`]),
//!    and an entry is never rebound, so user name resolution can't change
//!    it.
//! 3. A missing entry is an error naming the built-in, never a search of the
//!    names in scope.
//! 4. Entries are bound as their declarations are admitted, so prelude code
//!    after them can use the syntax.
//! 5. The registry is complete ([`check_complete`]) before any user code is
//!    elaborated: every *core* built-in ([`check_complete_core`]). A
//!    built-in's [`Home`] says whether its declaration is in the always-loaded
//!    core or in a library file (docs/proposals/std-library.md §4.6): a
//!    library built-in is bound when its file loads, and compiler code may
//!    use only core built-ins by identity, which a debug assertion checks.
//!
//! Binding a built-in only says which declaration is meant. Whether a native
//! implementation may replace it is decided separately, by the checks in
//! [`crate::native`], [`crate::partial`] and [`crate::chars`] (types, and
//! content hashes), which this doesn't weaken.

use std::collections::HashMap;

use stitchwort_syntax::Diagnostic;

use crate::globals::{Globals, State};
use crate::term::{DataId, DefId};

/// What kind of declaration a built-in is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Data,
    Def,
    /// A constructor of the given built-in data type.
    Ctor(Builtin),
}

/// Where a built-in's declaration lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Home {
    /// The always-loaded core: syntax, the checker, `deriving`, `calc` and
    /// abilities need it.
    Core,
    /// A library file, bound when that file loads (a native whose
    /// definition moved out of the core).
    Library,
}

/// The built-ins whose declaration is in a library file. Everything else is
/// in the core.
const LIBRARY: &[Builtin] = &[
    Builtin::IntTDiv,
    Builtin::IntTMod,
    Builtin::IntFDiv,
    Builtin::IntFMod,
    Builtin::IntModNat,
    Builtin::IntAbs,
    Builtin::IntToNatChecked,
    Builtin::IntSign,
    Builtin::NatToInt,
    Builtin::TextToInt,
    Builtin::TextToNat,
    Builtin::TextTrim,
    Builtin::TextSplit,
    Builtin::TextJoin,
    Builtin::TextLength,
    Builtin::TextIsEmpty,
    Builtin::TextUncons,
    Builtin::TextFold,
];

macro_rules! builtins {
    ($($variant:ident = $name:literal : $kind:expr,)*) => {
        /// A prelude declaration the compiler refers to.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Builtin {
            $($variant,)*
        }

        impl Builtin {
            pub const ALL: &'static [Builtin] = &[$(Builtin::$variant,)*];

            /// Its name in the prelude, from the library's root (`Std`): a
            /// data type's or definition's path, or a constructor's own name.
            pub fn name(self) -> &'static str {
                match self {
                    $(Builtin::$variant => $name,)*
                }
            }

            pub fn kind(self) -> Kind {
                use Kind::*;
                match self {
                    $(Builtin::$variant => $kind,)*
                }
            }

            /// Whether its declaration is in the core or a library file.
            pub fn home(self) -> Home {
                if LIBRARY.contains(&self) {
                    Home::Library
                } else {
                    Home::Core
                }
            }
        }
    };
}

builtins! {
    // Logic
    Void = "Void": Data,
    Unit = "Unit": Data,
    Trivial = "Trivial": Ctor(Builtin::Unit),
    Not = "Not": Def,
    // `p && q`, `p || q` on propositions
    And = "And": Data,
    Or = "Or": Data,
    Cong = "Eq.cong": Def,
    // `calc` chains combine their steps with these (`crates/elab/src/calc.rs`)
    EqSym = "Eq.sym": Def,
    EqTrans = "Eq.trans": Def,
    LeTrans = "Nat.leTrans": Def,
    LessTrans = "Nat.lessTrans": Def,
    // Numbers: syntax and natives
    Nat = "Nat": Data,
    Zero = "Zero": Ctor(Builtin::Nat),
    Succ = "Succ": Ctor(Builtin::Nat),
    Add = "Nat.add": Def,
    Sub = "Nat.sub": Def,
    Mul = "Nat.mul": Def,
    Div = "Nat.div": Def,
    Mod = "Nat.mod": Def,
    Leq = "Nat.leq": Def,
    LessEq = "Nat.LessEq": Def,
    LessThan = "Nat.LessThan": Def,
    EqNat = "Nat.equal": Def,
    EqNatRefl = "Nat.equalRefl": Def,
    EqNatSound = "Nat.equalSound": Def,
    NatNeq = "Nat.equalFalse": Def,
    DivFuel = "Nat.divFuel": Def,
    DecEqNat = "Nat.decEq": Def,
    // Integers
    Int = "Int": Data,
    OfNat = "OfNat": Ctor(Builtin::Int),
    NegSucc = "NegSucc": Ctor(Builtin::Int),
    IntNeg = "Int.neg": Def,
    IntAdd = "Int.add": Def,
    IntSub = "Int.sub": Def,
    IntMul = "Int.mul": Def,
    IntDiv = "Int.div": Def,
    IntMod = "Int.mod": Def,
    IntLessThan = "Int.LessThan": Def,
    IntLessEq = "Int.LessEq": Def,
    // Definitions with native JS (crates/js)
    IntTDiv = "Int.tdiv": Def,
    IntTMod = "Int.tmod": Def,
    IntFDiv = "Int.fdiv": Def,
    IntFMod = "Int.fmod": Def,
    IntModNat = "Int.modNat": Def,
    DecEqInt = "Int.decEq": Def,
    IntLeq = "Int.leq": Def,
    IntLess = "Int.less": Def,
    IntCompare = "Int.compare": Def,
    IntNatAbs = "Int.natAbs": Def,
    IntAbs = "Int.abs": Def,
    IntToNat = "Int.toNat": Def,
    IntToNatChecked = "Int.toNatChecked": Def,
    IntSign = "Int.sign": Def,
    NatToInt = "Nat.toInt": Def,
    IntToText = "Int.toText": Def,
    TextToInt = "Text.toInt": Def,
    // Booleans and decisions
    Bool = "Bool": Data,
    False = "False": Ctor(Builtin::Bool),
    True = "True": Ctor(Builtin::Bool),
    IfThenElse = "Bool.ifThenElse": Def,
    // `not`, by identity, so `not p` on a proposition can mean `Not p`
    BoolNot = "Bool.not": Def,
    Decidable = "Decidable": Data,
    Yes = "Yes": Ctor(Builtin::Decidable),
    No = "No": Ctor(Builtin::Decidable),
    FromYes = "Decidable.fromYes": Def,
    ToBool = "Decidable.toBool": Def,
    ElimDec = "Decidable.elim": Def,
    // Lists, `Option`, pairs
    List = "List": Data,
    Nil = "Nil": Ctor(Builtin::List),
    Cons = "Cons": Ctor(Builtin::List),
    Append = "List.append": Def,
    Option = "Option": Data,
    None = "None": Ctor(Builtin::Option),
    Some = "Some": Ctor(Builtin::Option),
    Pair = "Pair": Data,
    MkPair = "MkPair": Ctor(Builtin::Pair),
    Fst = "Pair.fst": Def,
    Snd = "Pair.snd": Def,
    // Characters and text
    Char = "Char": Data,
    MkChar = "MkChar": Ctor(Builtin::Char),
    // Any two proofs of `x = y` in `Bool` are equal: a char pattern's arm
    // uses it to make the matched character its literal (crates/elab,
    // `canonical`)
    BoolUniqueEq = "Bool.uniqueEq": Def,
    Text = "Text": Data,
    MkText = "MkText": Ctor(Builtin::Text),
    TextToList = "Text.toList": Def,
    TextFromList = "Text.fromList": Def,
    TextAppend = "Text.append": Def,
    TextLength = "Text.length": Def,
    TextIsEmpty = "Text.isEmpty": Def,
    DecEqText = "Text.decEq": Def,
    TextCompare = "Text.compare": Def,
    TextUncons = "Text.uncons": Def,
    TextFold = "Text.fold": Def,
    TextTrim = "Text.trim": Def,
    TextSplit = "Text.split": Def,
    TextJoin = "Text.join": Def,
    NatToText = "Nat.toText": Def,
    TextToNat = "Text.toNat": Def,
    // The effect machinery
    Comp = "Effect.Comp": Data,
    Done = "Done": Ctor(Builtin::Comp),
    Call = "Call": Ctor(Builtin::Comp),
    FoldComp = "Effect.foldComp": Def,
    Bind = "Effect.bind": Def,
    Plus = "Effect.Plus": Data,
    PlusRes = "Effect.PlusRes": Def,
    SigMap = "Effect.SigMap": Data,
    SigInject = "Effect.sigInject": Def,
    SigReply = "Effect.sigReply": Def,
    Translate = "Effect.translate": Def,
    SigId = "Effect.sigId": Def,
    SigCompose = "Effect.sigCompose": Def,
    SigLeft = "Effect.sigLeft": Def,
    SigRight = "Effect.sigRight": Def,
    UnitType = "Builtin.UnitType": Data,
    UnitValue = "UnitValue": Ctor(Builtin::UnitType),
    NoOp = "Effect.NoOp": Data,
    NoRes = "Effect.NoRes": Def,
    Sig = "Effect.Sig": Data,
    SigOp = "Effect.sigOp": Def,
    SigRes = "Effect.sigRes": Def,
    SigCase = "Effect.sigCase": Def,
    SigFromNo = "Effect.sigFromNo": Def,
    HandlePlus = "Effect.handlePlus": Def,
    RunPure = "Effect.runPure": Def,
    // Partial computations
    Rec = "Effect.Rec": Data,
    RecRes = "Effect.RecRes": Def,
    Delay = "Effect.Delay": Def,
    Now = "Effect.now": Def,
    Lift = "Effect.lift": Def,
    BindD = "Effect.bindD": Def,
    MapSig = "Effect.mapSig": Def,
    Pfix = "Effect.pfix": Def,
    // Input and output
    Io = "IO": Data,
    Print = "%print": Ctor(Builtin::Io),
    ReadLine = "%readLine": Ctor(Builtin::Io),
    ReadAll = "%readAll": Ctor(Builtin::Io),
    Simulate = "IO.simulate": Def,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Entry {
    Data(DataId),
    Def(DefId),
    Ctor(DataId, usize),
}

/// The bound built-ins.
#[derive(Default)]
pub struct Registry {
    entries: HashMap<Builtin, Entry>,
}

impl Registry {
    pub fn data(&self, b: Builtin) -> Option<DataId> {
        self.assert_usable(b);
        match self.entries.get(&b) {
            Some(Entry::Data(d)) => Some(*d),
            _ => None,
        }
    }

    pub fn def(&self, b: Builtin) -> Option<DefId> {
        self.assert_usable(b);
        match self.entries.get(&b) {
            Some(Entry::Def(id)) => Some(*id),
            _ => None,
        }
    }

    /// A constructor: its data type and index.
    pub fn ctor(&self, b: Builtin) -> Option<(DataId, usize)> {
        self.assert_usable(b);
        match self.entries.get(&b) {
            Some(Entry::Ctor(d, c)) => Some((*d, *c)),
            _ => None,
        }
    }

    /// Compiler code refers by identity only to built-ins that are in the
    /// core (a library file loads on demand, so a library built-in may not
    /// be bound yet): a library built-in is reached by name, through the
    /// loader.
    fn assert_usable(&self, b: Builtin) {
        debug_assert!(
            b.home() == Home::Core || self.entries.contains_key(&b),
            "compiler code uses the library built-in `{}` before its file loads",
            b.name()
        );
    }

    /// Whether `d` is built-in data type `b`.
    pub fn is_data(&self, b: Builtin, d: DataId) -> bool {
        self.data(b) == Some(d)
    }

    /// Whether `id` is built-in definition `b`.
    pub fn is_def(&self, b: Builtin, id: DefId) -> bool {
        self.def(b) == Some(id)
    }

    /// The built-in definition `id` is, if any.
    pub fn def_builtin(&self, id: DefId) -> Option<Builtin> {
        self.entries
            .iter()
            .find(|(_, e)| **e == Entry::Def(id))
            .map(|(b, _)| *b)
    }

    /// The built-ins not bound yet, in declaration order of [`Builtin`].
    pub fn missing(&self) -> Vec<Builtin> {
        Builtin::ALL
            .iter()
            .copied()
            .filter(|b| !self.entries.contains_key(b))
            .collect()
    }

    /// The core built-ins not bound yet.
    pub fn missing_core(&self) -> Vec<Builtin> {
        self.missing()
            .into_iter()
            .filter(|b| b.home() == Home::Core)
            .collect()
    }

    /// Forgets the built-ins bound to definitions from `defs` on and data
    /// types from `datas` on: for undoing declarations that are removed
    /// again (a check cache entry the kernel refused part of).
    pub fn forget_from(&mut self, defs: usize, datas: usize) {
        self.entries.retain(|_, e| match e {
            Entry::Def(id) => id.0 < defs,
            Entry::Data(d) | Entry::Ctor(d, _) => d.0 < datas,
        });
    }

    /// For a test of what depends on the registry: forgets entry `b`, as
    /// if the prelude didn't declare it.
    #[doc(hidden)]
    pub fn forget_for_test(&mut self, b: Builtin) {
        self.entries.remove(&b);
    }
}

/// Binds the built-in data type the prelude's final data type `d` is, if
/// any, with its constructors. Only for the prelude, as it loads.
pub fn bind_data(g: &mut Globals, d: DataId) -> Option<Builtin> {
    let data = g.data(d);
    if data.state != State::Final {
        return None;
    }
    let b = unbound(g, &data.name, |k| k == Kind::Data)?;
    let mut new = vec![(b, Entry::Data(d))];
    for &ctor in Builtin::ALL {
        if ctor.kind() == Kind::Ctor(b)
            && let Some(c) = data.ctors.iter().position(|c| &*c.name == ctor.name())
        {
            new.push((ctor, Entry::Ctor(d, c)));
        }
    }
    g.registry.entries.extend(new);
    Some(b)
}

/// Binds the built-in definition the prelude's final definition `id` is, if
/// any. Only for the prelude, as it loads.
pub fn bind_def(g: &mut Globals, id: DefId) -> Option<Builtin> {
    let def = g.def(id);
    if def.state != State::Final {
        return None;
    }
    let b = unbound(g, &def.name, |k| k == Kind::Def)?;
    g.registry.entries.insert(b, Entry::Def(id));
    Some(b)
}

fn unbound(g: &Globals, name: &str, kind: impl Fn(Kind) -> bool) -> Option<Builtin> {
    Builtin::ALL
        .iter()
        .copied()
        .find(|b| b.name() == name && kind(b.kind()))
        .filter(|b| !g.registry.entries.contains_key(b))
}

/// Refuses an incomplete registry: user code can't be elaborated until every
/// built-in is bound.
pub fn check_complete(g: &Globals) -> Result<(), Diagnostic> {
    complete(&g.registry.missing())
}

/// [`check_complete`] for the core built-ins only: what user code needs
/// before it is elaborated. A library built-in is bound when its file loads.
pub fn check_complete_core(g: &Globals) -> Result<(), Diagnostic> {
    complete(&g.registry.missing_core())
}

fn complete(missing: &[Builtin]) -> Result<(), Diagnostic> {
    if missing.is_empty() {
        return Ok(());
    }
    let names: Vec<String> = missing.iter().map(|b| format!("`{}`", b.name())).collect();
    Err(Diagnostic::error(
        "E-BUILTIN",
        format!(
            "the prelude doesn't declare what the compiler needs: {}",
            names.join(", ")
        ),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_distinct_per_kind() {
        for (i, a) in Builtin::ALL.iter().enumerate() {
            for b in &Builtin::ALL[i + 1..] {
                let same_kind = matches!(
                    (a.kind(), b.kind()),
                    (Kind::Data, Kind::Data) | (Kind::Def, Kind::Def)
                ) || matches!((a.kind(), b.kind()), (Kind::Ctor(x), Kind::Ctor(y)) if x == y);
                assert!(!(same_kind && a.name() == b.name()), "{a:?} and {b:?}");
            }
        }
    }

    #[test]
    fn constructors_belong_to_data_types() {
        for b in Builtin::ALL {
            if let Kind::Ctor(parent) = b.kind() {
                assert_eq!(parent.kind(), Kind::Data, "{b:?}");
            }
        }
    }
}
