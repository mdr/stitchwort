//! The built-in registry (docs/proposals/namespaces.md §4.7): the prelude
//! declarations that syntax, natives, the effect machinery, extraction, the
//! printer and the runner mean, by identity rather than by name.
//!
//! `a + b` means the prelude's `add`, whatever `add` means where it's
//! written; a user's own `List` never gets the list codec. Its invariants:
//!
//! 1. Each entry is a final declaration of these [`Kernel`], so ids are
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
//! 6. A definition that compiler code applies to arguments by position
//!    records its leading binders as a *shape* (`"[p] [a] d y n z yesEq
//!    noEq"`: implicit binders in brackets, names as declared, `_` for an
//!    anonymous one). Binding it refuses the library, with `E-BUILTIN`, if
//!    the declaration has other binders ([`check_shape`]); and the standard
//!    library must declare every library built-in
//!    ([`check_library_declares_all`]). Entries without a shape are not
//!    checked; adding one is how a call site gets protected. The empty shape
//!    `""` means the built-in takes its hypothesis directly (as
//!    `Bool.falseNotTrue h`): it's only checked to have no leading binders,
//!    not its statement, which the kernel checks at every use.
//!
//! Binding a built-in only says which declaration is meant. Whether a native
//! implementation may replace it is decided separately, by the checks in
//! [`crate::native`], [`crate::partial`] and [`crate::chars`] (types, and
//! content hashes), which this doesn't weaken.

use crate::collections::HashMap;
use crate::ev::Ev;
use crate::machine::in_kernel_modes;

use stitchwort_syntax::Diagnostic;

use crate::globals::{Kernel, State};
use crate::term::{DataId, DefId, Icit, Term};

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
    Builtin::TextTake,
    Builtin::TextDrop,
    Builtin::TextContains,
    Builtin::TextSplit,
    Builtin::TextJoin,
    Builtin::TextLength,
    Builtin::TextIsEmpty,
    Builtin::TextUncons,
    Builtin::TextFold,
    Builtin::Array,
    Builtin::ArraySize,
    Builtin::ArrayGet,
    Builtin::ArrayGetOr,
    Builtin::ArrayGetLt,
    Builtin::ArraySet,
    Builtin::ArrayPush,
    Builtin::ArrayPop,
    Builtin::ArrayReplicate,
    Builtin::SafeNat,
    Builtin::SafeInt,
    Builtin::Map,
    Builtin::MapFromList,
    Builtin::MapToList,
    Builtin::Float,
    Builtin::FloatAdd,
    Builtin::FloatSub,
    Builtin::FloatNeg,
    Builtin::FloatAbs,
    Builtin::FloatIsNaN,
    Builtin::FloatDecEq,
    Builtin::FloatIeeeEq,
    Builtin::FloatMul,
    Builtin::FloatDiv,
    Builtin::FloatRem,
    Builtin::FloatFloor,
    Builtin::FloatCeil,
    Builtin::FloatTrunc,
    Builtin::FloatRound,
    Builtin::FloatOfInt,
    Builtin::FloatOfNat,
    Builtin::FloatToText,
    Builtin::FloatIsFinite,
    Builtin::FloatIeeeLt,
    Builtin::FloatIeeeLe,
    Builtin::FloatToInt,
    Builtin::FloatCompare,
    Builtin::FloatLeq,
    Builtin::FloatLess,
    Builtin::FloatLessEq,
    Builtin::FloatLessThan,
    Builtin::FloatDecLessEq,
    Builtin::FloatDecLessThan,
    Builtin::Fin,
    Builtin::FZero,
    Builtin::FSucc,
    Builtin::FinOfNatLt,
    Builtin::FinToNat,
    Builtin::Fail,
    Builtin::FailStop,
    Builtin::NonEmptyList,
    Builtin::NonEmptyListPrependList,
];

macro_rules! builtins {
    ($($variant:ident = $name:literal : $kind:expr $(=> $shape:literal)?,)*) => {
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

            /// The leading binders of the stored type that Rust code builds
            /// applications with, as [`shape_of`] prints them, if the entry
            /// records them: checked when the declaration is bound
            /// ([`check_shape`]).
            pub fn shape(self) -> Option<&'static str> {
                match self {
                    $(Builtin::$variant => builtins!(@shape $($shape)?),)*
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
    (@shape) => { None };
    (@shape $shape:literal) => { Some($shape) };
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
    // Printed as the notation that writes them, `p ↔ q`, `∃ (x: T) => P`
    // and `x ∈ xs` (D1204)
    Iff = "Iff": Data,
    Exists = "Exists": Data,
    ListMem = "List.Mem": Def,
    Cong = "Eq.cong": Def => "[a] [b] f [x] [y] p",
    // `calc` chains combine their steps with these (`crates/elab/src/calc.rs`)
    EqSym = "Eq.sym": Def => "[a] [x] [y] p",
    EqTrans = "Eq.trans": Def => "[a] [x] [y] [z] p q",
    LeTrans = "Nat.leTrans": Def => "a b c h1 h2",
    LessTrans = "Nat.lessTrans": Def => "m n p h1 h2",
    // What `decreasing` generates refers to these (crates/elab/src/decreasing.rs)
    VoidAbsurd = "Void.absurd": Def => "[a] v",
    VoidExfalso = "Void.exfalso": Def => "[p] v",
    FalseNotTrue = "Bool.falseNotTrue": Def => "",
    LeRefl = "Nat.leRefl": Def => "n",
    ElimDecCong = "Decidable.elimCong": Def => "[p] [a] d y1 y2 n1 n2 sameYes sameNo",
    IfCong = "Bool.ifThenElseCong": Def => "[a] c t1 t2 e1 e2 sameThen sameElse",
    // and these for a lexicographic measure, `decreasing (m1, m2)`
    ElimDecEq = "Decidable.elimEq": Def => "[p] [a] d y n z yesEq noEq",
    ElimDecProof = "Decidable.elimProof": Def => "[p] [a] d ifYes ifNo",
    LexLess = "Nat.LexLess": Data,
    LexKeepsFirst = "Nat.lexKeepsFirst": Def => "a1 a2 b1 b2 k lex no h",
    LexSecondLess = "Nat.lexSecondLess": Def => "a1 a2 b1 b2 k lex no h",
    // Numbers: syntax and natives
    Nat = "Nat": Data,
    Zero = "Zero": Ctor(Builtin::Nat),
    Succ = "Succ": Ctor(Builtin::Nat),
    Add = "Nat.add": Def,
    // The theorems R3 and R4 of `+` are the equations of (`nat_add.rs`)
    NatAddZero = "Nat.addZero": Def => "n",
    NatAddSucc = "Nat.addSucc": Def => "n m",
    Sub = "Nat.sub": Def,
    Mul = "Nat.mul": Def,
    Div = "Nat.div": Def,
    Mod = "Nat.mod": Def,
    Leq = "Nat.leq": Def,
    LessEq = "Nat.LessEq": Def,
    LessThan = "Nat.LessThan": Def,
    // The standard decisions of `<=` and `<`: in a `Bool` they read as the
    // comparison itself (`Nat.leq`, `Int.leq`, `Int.less`), not as the `holds`
    // of them
    DecLessEqNat = "Nat.decLessEq": Def,
    DecLessThanNat = "Nat.decLessThan": Def,
    EqNat = "Nat.equal": Def,
    EqNatRefl = "Nat.equalRefl": Def,
    EqNatSound = "Nat.equalSound": Def,
    NatNeq = "Nat.equalFalse": Def,
    DivFuel = "Nat.divFuel": Def,
    // One step of `divFuel`, which goals show as the `/` it comes from
    DivStep = "Nat.divStep": Def,
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
    DecLessEqInt = "Int.decLessEq": Def,
    DecLessThanInt = "Int.decLessThan": Def,
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
    // Whole numbers that cross the JS boundary as a `number`
    // (std/Int/Safe.sw)
    SafeNat = "SafeNat": Data,
    SafeInt = "SafeInt": Data,
    // `Map Text V` crosses the JS boundary as a plain object (std/Map/Map.sw):
    // read and built with these, in the order of the library's `Text`
    // (DESIGN.md §12)
    Map = "Map": Data,
    MapFromList = "Map.fromList": Def,
    MapToList = "Map.toList": Def,
    TextInstOrd = "Text.instOrd": Def,
    // `Float`, a double (std/Float/Float.sw, crates/core/src/float.rs): the
    // type, its primitives, its definitions with natives, and the theorems
    // `Float.decEq`'s native refers to
    Float = "Float": Data,
    FloatAdd = "Float.add": Def,
    FloatSub = "Float.sub": Def,
    FloatNeg = "Float.neg": Def,
    FloatAbs = "Float.abs": Def,
    FloatIsNaN = "Float.isNaN": Def,
    FloatDecEq = "Float.decEq": Def,
    // JS's `===` on doubles: a native in the runtimes only
    FloatIeeeEq = "Float.ieeeEq": Def,
    FloatMul = "Float.mul": Def,
    FloatDiv = "Float.div": Def,
    FloatRem = "Float.rem": Def,
    FloatFloor = "Float.floor": Def,
    FloatCeil = "Float.ceil": Def,
    FloatTrunc = "Float.trunc": Def,
    FloatRound = "Float.round": Def,
    FloatOfInt = "Float.ofInt": Def,
    FloatOfNat = "Float.ofNat": Def,
    FloatToText = "Float.toText": Def,
    FloatIsFinite = "Float.isFinite": Def,
    FloatIeeeLt = "Float.ieeeLt": Def,
    FloatIeeeLe = "Float.ieeeLe": Def,
    FloatToInt = "Float.toInt": Def,
    // The total order: a native in the runtimes only
    FloatCompare = "Float.compare": Def,
    // The total order's `<=` and `<` as `Bool`s: natives in the runtimes only.
    // Their decisions (`Float.decLessEq`, `Float.decLessThan`) are written as
    // them where a `Bool` is wanted, as `Int`'s are (crates/elab/src/bind.rs),
    // and `x <= y` and `x < y` are decided by them as written
    FloatLeq = "Float.leq": Def,
    FloatLess = "Float.less": Def,
    FloatLessEq = "Float.LessEq": Def,
    FloatLessThan = "Float.LessThan": Def,
    FloatDecLessEq = "Float.decLessEq": Def,
    FloatDecLessThan = "Float.decLessThan": Def,
    // `Fin n`, the numbers below n (std/Fin/Fin.sw): a numeral `k` checked
    // against `Fin n` for a known n is `Fin.ofNatLt n k rfl`, and a number
    // pattern on one is `FZero` or `FSucc` (docs/proposals/fin-literals.md)
    Fin = "Fin": Data,
    FZero = "FZero": Ctor(Builtin::Fin),
    FSucc = "FSucc": Ctor(Builtin::Fin),
    FinOfNatLt = "Fin.ofNatLt": Def => "n i lt",
    // `Fin.toNat` and `Fin.ofNatLt` are the identity in the fast runtimes,
    // where a `Fin` is a number (`stitchwort_rt::natives::FinNative`)
    FinToNat = "Fin.toNat": Def,
    // A case that hypothesis `h: Less = Equal` rules out is filled in as
    // `Ordering.lessNotEqual h`, the term its written arm would be, not
    // with a helper of its own (crates/elab/src/cases.rs `contradiction`)
    Ordering = "Ordering": Data,
    OrderingLess = "Less": Ctor(Builtin::Ordering),
    OrderingEqual = "Equal": Ctor(Builtin::Ordering),
    OrderingGreater = "Greater": Ctor(Builtin::Ordering),
    LessNotEqual = "Ordering.lessNotEqual": Def => "",
    LessNotGreater = "Ordering.lessNotGreater": Def => "",
    EqualNotLess = "Ordering.equalNotLess": Def => "",
    EqualNotGreater = "Ordering.equalNotGreater": Def => "",
    GreaterNotLess = "Ordering.greaterNotLess": Def => "",
    GreaterNotEqual = "Ordering.greaterNotEqual": Def => "",
    // Booleans and decisions
    Bool = "Bool": Data,
    False = "False": Ctor(Builtin::Bool),
    True = "True": Ctor(Builtin::Bool),
    IfThenElse = "Bool.ifThenElse": Def => "[a] cond ifTrue ifFalse",
    // `not`, by identity, so `not p` on a proposition can mean `Not p`
    BoolNot = "Bool.not": Def,
    Decidable = "Decidable": Data,
    Holds = "Decidable.holds": Def => "[p] r",
    // `match h: c < x` on a comparison its decision reduces to `Bool.decTrue b`
    // for matches on `b` itself (crates/elab/src/matching.rs)
    DecTrue = "Bool.decTrue": Def => "b",
    ElimDec = "Decidable.elim": Def => "[p] [a] d ifYes ifNo",
    // `if p && q` whose branches use its proof (crates/elab/src/logic.rs),
    // and the parts of such a proof `auto` uses (crates/elab/src/auto.rs)
    DecAndThen = "Decidable.andThen": Def => "[p] [q] dp dq",
    AndLeft = "And.left": Def => "[p] [q] r",
    AndRight = "And.right": Def => "[p] [q] r",
    // `Ord.compare` of an instance the code names compiles to that
    // instance's comparison, read from its definition (crates/js): a
    // record, or `Ord.fromCompare` of one
    OrdCompare = "Ord.compare": Def,
    OrdFromCompare = "Ord.fromCompare": Def,
    // Lists, `Option`, pairs
    List = "List": Data,
    Nil = "Nil": Ctor(Builtin::List),
    Cons = "Cons": Ctor(Builtin::List),
    Append = "List.append": Def,
    // `List.length` runs as `List.lengthOnto xs 0`, a loop (`Def::run_body`)
    ListLengthOnto = "List.lengthOnto": Def,
    ListLength = "List.length": Def,
    Option = "Option": Data,
    None = "None": Ctor(Builtin::Option),
    Some = "Some": Ctor(Builtin::Option),
    // `NonEmptyList a` (std/NonEmptyList/NonEmptyList.sw): list literals and
    // list patterns build and match it where it is the expected type, and a
    // literal with spreads before its first item puts them in front with
    // `prependList` (docs/proposals/non-empty-lists.md §7)
    NonEmptyList = "NonEmptyList": Data,
    NonEmptyListPrependList = "NonEmptyList.prependList": Def => "[a] prefix xs",
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
    BoolUniqueEq = "Bool.uniqueEq": Def => "x y p q",
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
    TextTake = "Text.take": Def,
    TextDrop = "Text.drop": Def,
    TextContains = "Text.contains": Def,
    TextSplit = "Text.split": Def,
    TextJoin = "Text.join": Def,
    NatToText = "Nat.toText": Def,
    TextToNat = "Text.toNat": Def,
    // `Array` (std/Array/Array.sw): one buffer at run time, its operations
    // natives bound by content hash (crates/rt/src/natives.rs)
    Array = "Array": Data,
    ArraySize = "Array.size": Def,
    ArrayGet = "Array.get": Def,
    ArrayGetOr = "Array.getOr": Def,
    ArrayGetLt = "Array.getLt": Def,
    ArraySet = "Array.set": Def,
    ArrayPush = "Array.push": Def,
    ArrayPop = "Array.pop": Def,
    ArrayReplicate = "Array.replicate": Def,
    // The effect machinery
    Comp = "Effect.Comp": Data,
    Done = "Done": Ctor(Builtin::Comp),
    Call = "Call": Ctor(Builtin::Comp),
    FoldComp = "Effect.foldComp": Def => "[op] [res] [a] [r] done call comp",
    Bind = "Effect.bind": Def => "[op] [res] [a] [b] comp next",
    Plus = "Effect.Plus": Data,
    PlusRes = "Effect.PlusRes": Def => "[l] [r] lres rres o",
    SigMap = "Effect.SigMap": Data,
    SigInject = "Effect.sigInject": Def => "[op1] [res1] [op2] [res2] m o",
    SigReply = "Effect.sigReply": Def => "[op1] [res1] [op2] [res2] m o reply",
    Translate = "Effect.translate": Def => "[op1] [res1] [op2] [res2] [a] m comp",
    SigId = "Effect.sigId": Def => "[op] [res]",
    SigCompose = "Effect.sigCompose": Def => "[op1] [res1] [op2] [res2] [op3] [res3] first second",
    SigLeft = "Effect.sigLeft": Def => "[l] [r] [lres] [rres]",
    SigRight = "Effect.sigRight": Def => "[l] [r] [lres] [rres]",
    UnitType = "Builtin.UnitType": Data,
    UnitValue = "UnitValue": Ctor(Builtin::UnitType),
    NoOp = "Effect.NoOp": Data,
    NoRes = "Effect.NoRes": Def => "o",
    SigCase = "Effect.sigCase": Def => "[l] [r] [t] [lres] [rres] [tres] ml mr",
    SigFromNo = "Effect.sigFromNo": Def => "[t] [tres]",
    HandlePlus = "Effect.handlePlus": Def => "[l] [r] [lres] [rres] [res] fl fr o k",
    RunPure = "Effect.runPure": Def => "[a] comp",
    // Effect-row parameters (docs/proposals/effect-polymorphism.md, design C)
    Row = "Effect.Effects": Data,
    RowEmpty = "Empty": Ctor(Builtin::Row),
    RowOps = "Ops": Ctor(Builtin::Row),
    RowOp = "Effect.rowOp": Def => "row",
    RowRes = "Effect.rowRes": Def => "row o",
    CompIn = "Effect.CompIn": Def => "row a",
    DoneIn = "Effect.doneIn": Def => "[a] row x",
    BindIn = "Effect.bindIn": Def => "[a] [b] row comp next",
    LiftIn = "Effect.liftIn": Def => "[a] row comp",
    LowerIn = "Effect.lowerIn": Def => "[a] row comp",
    WidenIn = "Effect.widenIn": Def => "[a] pre preRes row m comp",
    // Partial computations
    Rec = "Effect.Rec": Data,
    RecRes = "Effect.RecRes": Def => "[req] ans rec",
    Delay = "Effect.Delay": Def => "op res a",
    Now = "Effect.now": Def => "[op] [res] [a] x",
    Lift = "Effect.lift": Def => "[op] [res] [a] comp",
    BindD = "Effect.bindD": Def => "[op] [res] [a] [b] delay next",
    MapSig = "Effect.mapSig": Def => "[op1] [res1] [op2] [res2] [a] m delay",
    Pfix = "Effect.pfix": Def => "[op] [res] [req] [ans] step x",
    FoldD = "Effect.foldD": Def => "[op1] [res1] [op2] [res2] [a] [b] done call delay",
    // Partiality through a bare row (docs/proposals/partial-stage-3.md)
    Divergence = "Effect.Divergence": Data,
    DivTotal = "Total": Ctor(Builtin::Divergence),
    DivMay = "MayDiverge": Ctor(Builtin::Divergence),
    CompD = "Effect.CompD": Def => "d row a",
    DoneD = "Effect.doneD": Def => "[a] d row x",
    BindDv = "Effect.bindDv": Def => "[a] [b] d row comp next",
    LiftD = "Effect.liftD": Def => "[a] d row comp",
    DelayD = "Effect.delayD": Def => "[a] d row comp",
    // Partiality through a row with abilities (docs/proposals/partial-handlers.md)
    FoldCompD = "Effect.foldCompD": Def => "[op1] [res1] [a] [b] d out done call comp",
    TranslateD = "Effect.translateD": Def => "[a] d from to m comp",
    CallD = "Effect.callD": Def => "[b] d row o k",
    // Input and output
    Io = "IO": Data,
    Print = "%print": Ctor(Builtin::Io),
    ReadLine = "%readLine": Ctor(Builtin::Io),
    ReadAll = "%readAll": Ctor(Builtin::Io),
    // Terminal control (docs/proposals/terminal-io.md §4.2): what a runner
    // performs, and `IO.console`'s reply, a record the runners build
    IoConsole = "%console": Ctor(Builtin::Io),
    KeysMode = "%keysMode": Ctor(Builtin::Io),
    ReadBytes = "%readBytes": Ctor(Builtin::Io),
    IoWrite = "%write": Ctor(Builtin::Io),
    Console = "Console": Data,
    RandomSeed = "%randomSeed": Ctor(Builtin::Io),
    Args = "%args": Ctor(Builtin::Io),
    Simulate = "IO.simulate": Def => "[e] [%div.e] [a] input prog",
    // `Fail` (std/Fail/Fail.sw): a `main` may leave it unhandled, and the
    // runners perform `stop` themselves, as they perform `print`
    // (docs/proposals/partial-stage-2.md)
    Fail = "Fail": Data,
    FailStop = "%stop": Ctor(Builtin::Fail),
}

/// The built-in data types with a JavaScript boundary form of their own
/// (DESIGN.md §12), not the tagged objects a data type crosses as: a codec
/// written for them, which `js.*` attributes couldn't change, so none may be
/// written on them (docs/proposals/attributes.md §4.2, D613). The one list
/// the elaborator and the JS backend both read.
pub const BOUNDARY_FORMS: &[Builtin] = &[
    Builtin::Nat,
    Builtin::Int,
    Builtin::SafeNat,
    Builtin::SafeInt,
    Builtin::Bool,
    Builtin::Text,
    Builtin::Char,
    Builtin::List,
    Builtin::Option,
    Builtin::Map,
    Builtin::Float,
];

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
    /// A library is installed, so a built-in of it that isn't bound yet is
    /// only not loaded: a program may still use it, and a message may name it.
    library: bool,
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

    /// Built-in data type `b` if it is bound yet: for a library built-in,
    /// whose file may not have loaded (see [`Registry::loaded_def`]).
    pub fn loaded_data(&self, b: Builtin) -> Option<DataId> {
        match self.entries.get(&b) {
            Some(Entry::Data(d)) => Some(*d),
            _ => None,
        }
    }

    /// Records that a library is installed (see [`Registry::library_installed`]).
    pub(crate) fn install_library(&mut self) {
        self.library = true;
    }

    /// Whether a library is installed, loaded or not.
    pub fn library_installed(&self) -> bool {
        self.library
    }

    /// Every binding, in [`Builtin`]'s order: for the check cache's
    /// canonical dump and for checking an undo. Unlike [`Registry::def`]
    /// and [`Registry::data`], it reads a library built-in whose file
    /// hasn't loaded too.
    pub fn dump(&self, out: &mut String) {
        use std::fmt::Write;
        let Registry { entries, library } = self;
        let _ = writeln!(out, "registry library {library}");
        for b in Builtin::ALL {
            match entries.get(b) {
                Some(Entry::Def(id)) => {
                    let _ = writeln!(out, "builtin {b:?} = def {}", id.0);
                }
                Some(Entry::Data(d)) => {
                    let _ = writeln!(out, "builtin {b:?} = data {}", d.0);
                }
                Some(Entry::Ctor(d, c)) => {
                    let _ = writeln!(out, "builtin {b:?} = ctor {} {c}", d.0);
                }
                None => {}
            }
        }
    }

    /// Built-in definition `b` if it is bound yet. Unlike [`Registry::def`]
    /// this is for a library built-in too: it asks whether the library file
    /// that declares `b` has loaded, and a program that hasn't loaded it
    /// can't refer to it, so "not bound" is an answer, not a bug.
    pub fn loaded_def(&self, b: Builtin) -> Option<DefId> {
        match self.entries.get(&b) {
            Some(Entry::Def(id)) => Some(*id),
            _ => None,
        }
    }

    /// Built-in constructor `b` if its library file has loaded. Like
    /// [`Registry::loaded_def`], for a caller that may run before the file
    /// that declares `b` does: "not bound" is an answer, not a bug.
    pub fn loaded_ctor(&self, b: Builtin) -> Option<(DataId, usize)> {
        match self.entries.get(&b) {
            Some(Entry::Ctor(d, c)) => Some((*d, *c)),
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

    /// The built-in data type `d` is, if it has a boundary form of its own
    /// ([`BOUNDARY_FORMS`]). The elaborator refuses `js.*` attributes on
    /// such a type, and the JS backend picks its codec by it (confirming
    /// the declaration by content hash where the codec depends on it).
    pub fn boundary_form(&self, d: DataId) -> Option<Builtin> {
        BOUNDARY_FORMS
            .iter()
            .copied()
            .find(|b| self.entries.get(b) == Some(&Entry::Data(d)))
    }

    /// Whether `d` is built-in data type `b`. False while `b`'s library file
    /// hasn't loaded: a type that exists can't be one that doesn't.
    pub fn is_data(&self, b: Builtin, d: DataId) -> bool {
        self.loaded_data(b) == Some(d)
    }

    /// Whether `id` is built-in definition `b`. False while `b`'s library
    /// file hasn't loaded.
    pub fn is_def(&self, b: Builtin, id: DefId) -> bool {
        self.loaded_def(b) == Some(id)
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
    pub(crate) fn forget_from(&mut self, defs: usize, datas: usize) {
        self.entries.retain(|_, e| match e {
            Entry::Def(id) => id.0 < defs,
            Entry::Data(d) | Entry::Ctor(d, _) => d.0 < datas,
        });
    }
}

impl Registry {
    /// For a test of what depends on the registry: forgets entry `b`, as
    /// if the prelude didn't declare it.
    #[cfg(feature = "test-bypass")]
    pub(crate) fn forget_for_test(&mut self, b: Builtin) {
        self.entries.remove(&b);
    }
}

/// Records that a library is installed (see [`Registry::library_installed`]):
/// the one write to the registry from outside the kernel's declarations.
pub fn install_library(g: &mut Kernel) {
    in_kernel_modes(g, |g| {
        g.env.registry_mut().install_library();
    })
}

/// Binds the built-in data type the prelude's final data type `d` is, if
/// any, with its constructors. Only for the prelude, as it loads.
pub fn bind_data(g: &mut Kernel, d: DataId) -> Option<Builtin> {
    in_kernel_modes(g, |g| {
        let data = g.data(d);
        if data.state != State::Final {
            return None;
        }
        let b = unbound(&g.ev(), &data.name, |k| k == Kind::Data)?;
        let mut new = vec![(b, Entry::Data(d))];
        for &ctor in Builtin::ALL {
            if ctor.kind() == Kind::Ctor(b)
                && let Some(c) = data.ctors.iter().position(|c| &*c.name == ctor.name())
            {
                new.push((ctor, Entry::Ctor(d, c)));
            }
        }
        g.env.registry_mut().entries.extend(new);
        Some(b)
    })
}

/// Binds the built-in definition the prelude's final definition `id` is, if
/// any. Only for the prelude, as it loads.
pub fn bind_def(g: &mut Kernel, id: DefId) -> Option<Builtin> {
    in_kernel_modes(g, |g| {
        let def = g.def(id);
        if def.state != State::Final || def.assumption().is_some() {
            return None;
        }
        let b = unbound(&g.ev(), &def.name, |k| k == Kind::Def)?;
        g.env.registry_mut().entries.insert(b, Entry::Def(id));
        Some(b)
    })
}

/// The leading binders of a stored type, one word each: `[x]` for an
/// implicit binder, `[auto x]` for an auto one, `x` for an explicit one, and
/// `_` for an anonymous name. This is what a [`Builtin::shape`] is written in.
/// Read without unfolding anything: a definition whose type is a name for a
/// function type has no binders here.
pub fn shape_of(ty: &Term) -> String {
    let mut words: Vec<String> = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, icit, _, body) = t {
        let name = if name.is_empty() || name.starts_with('_') {
            "_"
        } else {
            name
        };
        words.push(match icit {
            Icit::Explicit => name.to_string(),
            Icit::Implicit => format!("[{name}]"),
            Icit::Auto => format!("[auto {name}]"),
        });
        t = body.strip_loc();
    }
    words.join(" ")
}

/// Refuses definition `id`, bound as `b`, unless its leading binders are the
/// ones `b`'s shape says the compiler's code applies it to. A built-in with
/// no shape isn't checked. Like a stale pin, a mismatch is the library's
/// fault only in that it changed under the compiler: the fix is to update the
/// row in this file and the code that builds calls from it.
pub fn check_shape(g: &mut Kernel, id: DefId, b: Builtin) -> Result<(), Diagnostic> {
    let Some(expected) = b.shape() else {
        return Ok(());
    };
    #[cfg(feature = "test-bypass")]
    SHAPE_CHECKS.with(|c| c.borrow_mut().push(b));
    in_kernel_modes(g, |g| {
        let def = g.def(id);
        let found = shape_of(&def.ty);
        if found == expected {
            return Ok(());
        }
        Err(Diagnostic::error(
            "E-BUILTIN",
            format!(
                "the library's `{}` doesn't have the arguments the compiler builds it with: \
                 expected `{expected}`, found `{found}`",
                b.name()
            ),
        )
        .with_label(def.span, "declared here")
        .with_note(
            "if this change was meant, update the shape of this built-in in \
             crates/core/src/registry.rs and the code that applies it",
        ))
    })
}

#[cfg(feature = "test-bypass")]
thread_local! {
    static SHAPE_CHECKS: std::cell::RefCell<Vec<Builtin>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The built-ins [`check_shape`] has checked on this thread since the last
/// call: for the test that every shape is reached at binding.
#[cfg(feature = "test-bypass")]
#[doc(hidden)]
pub fn take_shape_checks() -> Vec<Builtin> {
    SHAPE_CHECKS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// Refuses a library that doesn't declare every library built-in: `owner`
/// says which library file declares a name (a constructor counts as declared
/// with its data type; its own binding is checked as the file loads). Without this a renamed library
/// declaration is found out when something first loads its file.
pub fn check_library_declares_all(owner: impl Fn(&str) -> Option<usize>) -> Result<(), Diagnostic> {
    let missing: Vec<Builtin> = Builtin::ALL
        .iter()
        .copied()
        .filter(|b| {
            // A constructor is declared with its data type.
            let declared = match b.kind() {
                Kind::Ctor(parent) => parent,
                _ => *b,
            };
            b.home() == Home::Library && owner(declared.name()).is_none_or(|f| f == 0)
        })
        .collect();
    complete(&missing)
}

fn unbound(g: &Ev, name: &str, kind: impl Fn(Kind) -> bool) -> Option<Builtin> {
    Builtin::ALL
        .iter()
        .copied()
        .find(|b| b.name() == name && kind(b.kind()))
        .filter(|b| !g.env.registry().entries.contains_key(b))
}

/// Refuses an incomplete registry: user code can't be elaborated until every
/// built-in is bound.
pub fn check_complete(g: &Ev) -> Result<(), Diagnostic> {
    complete(&g.env.registry().missing())
}

/// [`check_complete`] for the core built-ins only: what user code needs
/// before it is elaborated. A library built-in is bound when its file loads.
pub fn check_complete_core(g: &Ev) -> Result<(), Diagnostic> {
    complete(&g.env.registry().missing_core())
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

    /// A library constructor that no file has bound yet is "not loaded", not a
    /// panic: the missing-case search asks before any `Fin` code loads.
    #[test]
    fn an_unloaded_library_constructor_is_not_loaded() {
        let registry = Registry::default();
        assert_eq!(registry.loaded_ctor(Builtin::FSucc), None);
    }

    #[test]
    fn a_library_without_a_library_builtin_is_refused() {
        let all = check_library_declares_all(|_| Some(1));
        assert!(all.is_ok());
        let without = check_library_declares_all(|n| (n != "Int.tdiv").then_some(1));
        let message = without.unwrap_err().message;
        assert!(message.contains("`Int.tdiv`"), "{message}");
        // A core declaration doesn't stand in for a library one.
        assert!(check_library_declares_all(|_| Some(0)).is_err());
    }

    #[test]
    fn every_shape_is_well_formed() {
        for b in Builtin::ALL {
            let Some(shape) = b.shape() else { continue };
            assert_eq!(b.kind(), Kind::Def, "{b:?}: only definitions have shapes");
            assert_eq!(
                shape.matches('[').count(),
                shape.matches(']').count(),
                "{b:?}: {shape}"
            );
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
