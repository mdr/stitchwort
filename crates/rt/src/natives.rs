//! Which prelude declarations a backend may replace with native code, shared
//! by the JS backend (`crates/js`) and the runtime's lowering (D389).
//!
//! A native representation or operation is bound to a prelude declaration
//! by that declaration's content hash (DESIGN.md §11), which covers
//! everything it depends on: if the prelude changes, the declaration is
//! compiled as written instead (slower, but still right), and a test fails
//! until each native has been checked against the changed declaration and
//! its hash updated here. The natives' meaning is fixed here; each backend
//! has its own code for them (the JS backend's strings, the runtime's Rust).

use std::collections::HashMap;

use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::native;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Globals, Limits, ResourceError};

/// A prelude text operation with a native implementation, where a `Text` is
/// a native string (in JS, with the backend's `Options::native_text`). Like the
/// number natives, these are trusted, and tested against the definitions
/// they replace (`crates/cli/tests/extract.rs`). Each works on Unicode scalar
/// values, never on UTF-16 code units, and none uses JS stack space
/// proportional to the length of a text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TextNative {
    TextToList,
    TextFromList,
    TextAppend,
    TextLength,
    TextIsEmpty,
    DecEqText,
    TextCompare,
    TextUncons,
    TextFold,
    TextTrim,
    TextSplit,
    TextJoin,
    NatToText,
    TextToNat,
}

/// Each text native, the prelude definition it replaces, and that
/// definition's content hash (DESIGN.md §11), which covers everything it
/// depends on. A native is only used for a definition with exactly that hash,
/// so if the prelude changes, the definition is compiled as written instead:
/// slower, but still right. A test fails until each native has been checked
/// against the changed definition and its hash updated here.
const TEXT_NATIVES: &[(Builtin, TextNative, &str)] = &[
    (
        Builtin::TextToList,
        TextNative::TextToList,
        "5abb3da49e0fc62dcfa21f87af3b215730957c07d9549ca3dc2842d6c23d7a27",
    ),
    (
        Builtin::TextFromList,
        TextNative::TextFromList,
        "8104e7afa0a8a50d79e4669b0b3a8b65667ce412f2f0e09a84c94c35356384bf",
    ),
    (
        Builtin::TextAppend,
        TextNative::TextAppend,
        "1f34a024df4b7c9cfc3a3fc147e931f14b035c3224988493b469e3a8bfaf0467",
    ),
    (
        Builtin::TextLength,
        TextNative::TextLength,
        "2647eb8b8cbfb640c41d3b803d33a89765e51750f748e1f97f7b28db5259bb32",
    ),
    (
        Builtin::TextIsEmpty,
        TextNative::TextIsEmpty,
        "1889f230286963cff75856361014388b31f5036d649d9ac0f3f188b5b4af4661",
    ),
    (
        Builtin::DecEqText,
        TextNative::DecEqText,
        "c7fb4f69c407e2f9d1871c072e520121830c61cee8f6a799cee60b20962f2504",
    ),
    (
        Builtin::TextCompare,
        TextNative::TextCompare,
        "3a98f1aac6fcb288efa78b2f848214ce19e9146665b0397fb0392aae3f90d37d",
    ),
    (
        Builtin::TextUncons,
        TextNative::TextUncons,
        "dc12eccdfb2e03e842ead8377f4a9ab1fd8cce57d740cdc8922e3c002b133d58",
    ),
    (
        Builtin::TextFold,
        TextNative::TextFold,
        "0ab7473b8324d4ea62a176128301c5330ed1cc45f5ec9cd842342e0770ce707d",
    ),
    (
        Builtin::TextTrim,
        TextNative::TextTrim,
        "ec78b83ebc8635cb689fec17a0d5bc87423a45979d3b4496a68fe995afc37124",
    ),
    (
        Builtin::TextSplit,
        TextNative::TextSplit,
        "32813a7f4a37ba5e82e699bfe6763cce7639880f45beaae1f9525305ff996099",
    ),
    (
        Builtin::TextJoin,
        TextNative::TextJoin,
        "fbf17affece916ba221e97a7b061f3fb99d5d4c801cc9fc8b607b9549cb3e974",
    ),
    (
        Builtin::NatToText,
        TextNative::NatToText,
        "5d782d77af9a709c7532a26ad5b9bcdea82f980455e35fd4a5be785156403fac",
    ),
    (
        Builtin::TextToNat,
        TextNative::TextToNat,
        "40b834208c0b6345e3b81e200440e69bfc6969c2018de11d932c3c11d18587ed",
    ),
];

/// Whether a native applies to the program's definition of that name.
pub struct NativeBinding<N> {
    pub name: &'static str,
    pub native: N,
    /// The definition, if there is one.
    pub id: Option<DefId>,
    /// Its content hash, in hex.
    pub hash: Option<String>,
    /// Whether it's the definition the native was written for.
    pub bound: bool,
}

pub type TextBinding = NativeBinding<TextNative>;

/// Matches each native in `table` with the definition it replaces, by
/// content hash.
fn bind_natives<N: Copy>(
    g: &Globals,
    table: &[(Builtin, N, &str)],
) -> Result<Vec<NativeBinding<N>>, ResourceError> {
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    table
        .iter()
        .map(|&(builtin, native, expected)| {
            // Natives are mostly library built-ins, whose file may not have
            // loaded: then the program has no such definition to replace.
            let id = g.registry.loaded_def(builtin);
            let hash = match id {
                Some(id) => def_hash(g, id)?.map(|h| h.hex()),
                None => None,
            };
            Ok(NativeBinding {
                name: builtin.name(),
                native,
                id,
                bound: hash.as_deref() == Some(expected),
                hash,
            })
        })
        .collect()
}

/// Matches each text native with the definition it replaces, by content hash.
pub fn bind_text_natives(g: &Globals) -> Result<Vec<TextBinding>, ResourceError> {
    bind_natives(g, TEXT_NATIVES)
}

/// The content hash (DESIGN.md §11) of the prelude's `Int`, which the
/// `bigint` representation was written for. It covers the constructors,
/// their order, names and fields, and `Nat`. The representation is one
/// contract with its constructors' and matching's JS, the boundary codec,
/// the `.d.ts` type and every integer native, so all of those apply exactly
/// when this matches; otherwise `Int` is compiled as the ordinary data type
/// it is, with the ordinary codec (docs/proposals/integers.md, "Two separate
/// fallbacks"). A test fails until the representation has been checked
/// against a changed `Int` and this updated.
const INT_DATA_HASH: &str = "428aec701d06adbd62795fdbc01b7976c1beac83cdcb385d8d4eaebd14ce4b30";

/// The content hash (DESIGN.md §11) of the prelude's `Nat`, which the
/// `bigint` representation was written for. It covers the constructors,
/// their order, names and fields. The representation is one contract with
/// its constructors' and matching's JS, the boundary codec and the native
/// number operations, so all of those apply exactly when this matches;
/// otherwise `Nat` is compiled as the ordinary data type it is, with the
/// ordinary codec and its operations from their definitions. A test fails
/// until the representation has been checked against a changed `Nat` and
/// this updated.
pub const NAT_DATA_HASH: &str = "281ae0d5e9e49941a6eddd8b4d6b3f3f38a80ea3f95f9692e66096aae10040f5";

/// The content hash (DESIGN.md §11) of the prelude's `Text`, which the JS
/// string representation was written for. It covers its constructor, its
/// name and field, and `List` and `Char`. The representation is one contract
/// with its constructors' and matching's JS, the boundary codec, the `.d.ts`
/// type and every text native, so all of those apply exactly when this
/// matches; otherwise `Text` is compiled as the ordinary data type it is,
/// with the ordinary codec (docs/proposals/compact-text.md, option A), and
/// `run --js`, which requires it, refuses. A test fails until the
/// representation has been checked against a changed `Text` and this
/// updated.
pub const TEXT_DATA_HASH: &str = "6ef35ae8fd60047c2bd97ae3fb36e41fabbd60db16bedb2b8c88067372cc65e5";

/// Whether the `bigint` representation applies to the program's `Int`, and
/// which integer natives apply to its definitions.
pub struct IntBinding {
    /// The prelude's `Int`, if there is one.
    pub data: Option<DataId>,
    /// Its content hash, in hex.
    pub hash: Option<String>,
    /// Whether it's the data type the representation was written for.
    pub bound: bool,
    /// Each native, whether or not the representation applies: a native is
    /// used only if both its definition and the representation are bound.
    pub natives: Vec<NativeBinding<IntNative>>,
}

/// Matches the `bigint` representation with the prelude's `Int`, and each
/// integer native with the definition it replaces, by content hash.
pub fn bind_int(g: &Globals) -> Result<IntBinding, ResourceError> {
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let data = g.registry.data(Builtin::Int);
    let hash = match data {
        Some(d) => data_hash(g, d)?.map(|h| h.hex()),
        None => None,
    };
    Ok(IntBinding {
        data,
        bound: hash.as_deref() == Some(INT_DATA_HASH),
        hash,
        natives: bind_natives(g, INT_NATIVES)?,
    })
}

/// The prelude's `Int`, if the `bigint` representation applies to it
/// ([`bind_int`]). Hashing a checked data type with two constructors of one
/// field each takes a few stack frames, and the hash is remembered.
pub fn int_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.data(Builtin::Int)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Int` ran out of resources")?;
    (hash.hex() == INT_DATA_HASH).then_some(d)
}

/// The prelude's `Nat`, if the `bigint` representation applies to it
/// ([`NAT_DATA_HASH`]). Hashing a checked data type takes a few stack frames,
/// and the hash is remembered.
pub fn nat_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.data(Builtin::Nat)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Nat` ran out of resources")?;
    (hash.hex() == NAT_DATA_HASH).then_some(d)
}

/// The prelude's `Text`, if the JS string representation applies to it
/// ([`TEXT_DATA_HASH`]). Hashing a checked data type takes a few stack
/// frames, and the hash is remembered.
pub fn text_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.data(Builtin::Text)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Text` ran out of resources")?;
    (hash.hex() == TEXT_DATA_HASH).then_some(d)
}

/// The content hash of the library's `SafeNat` (std/Int/Safe.sw), which the
/// JS `number` codec was written for. It covers the field names and types
/// and the bound in the proof field, so the codec's range check and the type
/// agree exactly when this matches; otherwise `SafeNat` is an ordinary record
/// at the boundary (with a `bigint` field). A test fails until the codec has
/// been checked against a changed `SafeNat` and this updated.
pub const SAFE_NAT_HASH: &str = "85a218ab4335f853f23a5970eef0042ad79b979333b57c13b1400ef39bd29bd5";

/// The content hash of the library's `SafeInt`, as [`SAFE_NAT_HASH`].
pub const SAFE_INT_HASH: &str = "f83abb645b0b44d517077c186e28726771d9394db53853820765ca4f4962708a";

/// The library's `SafeNat`, if its file is loaded and the `number` codec
/// applies to it ([`SAFE_NAT_HASH`]).
pub fn safe_nat_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.loaded_data(Builtin::SafeNat)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `SafeNat` ran out of resources")?;
    (hash.hex() == SAFE_NAT_HASH).then_some(d)
}

/// The library's `SafeInt`, if its file is loaded and the `number` codec
/// applies to it ([`SAFE_INT_HASH`]).
pub fn safe_int_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.loaded_data(Builtin::SafeInt)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `SafeInt` ran out of resources")?;
    (hash.hex() == SAFE_INT_HASH).then_some(d)
}

/// A prelude integer operation with a native implementation, where an `Int`
/// is a native number (in JS a `bigint`, with the backend's
/// `Options::native_int`). Like the
/// number and text natives, these are trusted, and tested against the
/// definitions they replace (`crates/cli/tests/extract.rs`). A division's
/// proof that the divisor isn't zero is erased, but it exists (or an
/// export's precondition check has just established it), so none of these
/// divides by zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntNative {
    NatToInt,
    IntNeg,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntTDiv,
    IntTMod,
    IntFDiv,
    IntFMod,
    IntModNat,
    DecEqInt,
    IntLeq,
    IntLess,
    IntCompare,
    IntNatAbs,
    IntAbs,
    IntToNat,
    IntToNatChecked,
    IntSign,
    IntToText,
    TextToInt,
}

impl IntNative {
    /// Whether it also assumes that a `Text` is a native string.
    pub fn uses_text(self) -> bool {
        matches!(self, IntNative::IntToText | IntNative::TextToInt)
    }
}

/// Each integer native, the prelude definition it replaces, and that
/// definition's content hash, as for [`TEXT_NATIVES`].
const INT_NATIVES: &[(Builtin, IntNative, &str)] = &[
    (
        Builtin::NatToInt,
        IntNative::NatToInt,
        "6e9973e4558cd61d9f97a8a168d3c7c644ee38be27a43c1eb32cc4b60338cb98",
    ),
    (
        Builtin::IntNeg,
        IntNative::IntNeg,
        "347cfafd037525c1413df9f8db0642268050cebc4d5f9b45bb402e53f4c828cd",
    ),
    (
        Builtin::IntAdd,
        IntNative::IntAdd,
        "8e3611484f01b9db8555c2ad9d374082dabdda2863f293adbf109a7dc248eb7f",
    ),
    (
        Builtin::IntSub,
        IntNative::IntSub,
        "5f86c2911011a929b23204a693c68c066b16c39839417876e6e53f96ee9b66f9",
    ),
    (
        Builtin::IntMul,
        IntNative::IntMul,
        "62c9c6f96f3e064a133a3d3c51deface622fde015c6eef3a4a9cff45a5d71e71",
    ),
    (
        Builtin::IntDiv,
        IntNative::IntDiv,
        "6fb60aaf472c17c6bc9ecd3a68ec69ff2b4ddc99950a5c9ff34783371ee43958",
    ),
    (
        Builtin::IntMod,
        IntNative::IntMod,
        "ac4633f8435bedb90554849d7e1808da81fde5289ffd35077689e0b5c93e9440",
    ),
    (
        Builtin::IntTDiv,
        IntNative::IntTDiv,
        "5ebf56573fa6c6481defbfbabbb7bbbf7c86108e625f55bb14feb7378ace0f14",
    ),
    (
        Builtin::IntTMod,
        IntNative::IntTMod,
        "3575c974d3cba5365faa91dbbdb9f203586ef03d3c8af09f43dcd7017a426ceb",
    ),
    (
        Builtin::IntFDiv,
        IntNative::IntFDiv,
        "ac60444781afd5dc0f2404c720904cbfe3b81d7e35314965137a208dbd7afed2",
    ),
    (
        Builtin::IntFMod,
        IntNative::IntFMod,
        "d0eac438c0bb4193f1249625e7509e1ea6eca61dae63d3d085784ae424c4ab18",
    ),
    (
        Builtin::IntModNat,
        IntNative::IntModNat,
        "526deb729a9528f5d060fe8eb5b51dbeb95a766aeced14e791e9b03debdfb797",
    ),
    (
        Builtin::DecEqInt,
        IntNative::DecEqInt,
        "bfb9d75432dc4f02599ca684c24b40096a63cafc987808a93c5fe28d31371f8b",
    ),
    (
        Builtin::IntLeq,
        IntNative::IntLeq,
        "1076606963454e39dc191da34bbe1321ba54284d5597a50451af3b9c10ebcac6",
    ),
    (
        Builtin::IntLess,
        IntNative::IntLess,
        "206176cbbaa05dc2f9486d7e52c86aedf381cbd28945f337f26e73928221763b",
    ),
    (
        Builtin::IntCompare,
        IntNative::IntCompare,
        "ef69f80765a9b9cca880a9c260b0c82b3521fde01f4cacdcea76eeca685f7212",
    ),
    (
        Builtin::IntNatAbs,
        IntNative::IntNatAbs,
        "ba7abe1722616144bdd8c853b8857234cde73e16cb804dfaa9a0338bbdd6c50a",
    ),
    (
        Builtin::IntAbs,
        IntNative::IntAbs,
        "9c9c66ca4fbfca3668de18a91351c4cea27ae57b6ebaa13c4111d33ec857efb0",
    ),
    (
        Builtin::IntToNat,
        IntNative::IntToNat,
        "d0f20cf7ee0670bdf8d81e3d82f871e7c3ea860c70494bc39158cd5ca213dfe7",
    ),
    (
        Builtin::IntToNatChecked,
        IntNative::IntToNatChecked,
        "c547e9888ac69af472db81dd6d5d8ad4c37eb090e69144d1c0c72eff07e8634c",
    ),
    (
        Builtin::IntSign,
        IntNative::IntSign,
        "a4532fc4f0fcf19b83dea6cda7a6a42c58e90621c6da5f646036d1224ccaf65e",
    ),
    (
        Builtin::IntToText,
        IntNative::IntToText,
        "8c74404e1ba5d6e5e34f8fad9d1560a2992b8554149c04312a1903cbb679ae95",
    ),
    (
        Builtin::TextToInt,
        IntNative::TextToInt,
        "57c98cd6c3cbc6820ef468b322008a44bbc462168c937464a6feec872de35e7c",
    ),
];

/// A `Float` operation with a native implementation, where a `Float` is a
/// native double (a Rust `f64`, a JS `number`; docs/proposals/float.md
/// §3.5). The primitives (`add`, `round`, `ofInt`, …) have no definition,
/// and the kernel computes them the same way (`stitchwort_core::float`),
/// except `toText`, which only the runtimes compute; `neg`, `abs`, `isNaN`,
/// `isFinite`, `decEq`, `ieeeLt`, `ieeeLe` and `toInt` are the definitions
/// the kernel has natives for, bound there by content hash; `ieeeEq` and
/// `compare` are bound here ([`FLOAT_NATIVES`]). `FromBits` and `Bits` are the record's constructor
/// and its `bits` field, through the canonical bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatPrim {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Floor,
    Ceil,
    Trunc,
    Round,
    OfInt,
    OfNat,
    /// JS's `String(x)`: the runtimes' own `Float.toText`, which the kernel
    /// doesn't compute.
    ToText,
    Neg,
    Abs,
    IsNaN,
    IsFinite,
    DecEq,
    IeeeEq,
    IeeeLt,
    IeeeLe,
    ToInt,
    /// The total order (`Float.compare`).
    Compare,
    /// `{ bits = b, valid = _ }`: the double with bits `b`, which the
    /// record's proof says is a valid pattern.
    FromBits,
    /// `x.bits`: the double's bits, the NaN canonical.
    Bits,
}

impl FloatPrim {
    pub fn arity(self) -> u32 {
        match self {
            FloatPrim::Add
            | FloatPrim::Sub
            | FloatPrim::Mul
            | FloatPrim::Div
            | FloatPrim::Rem
            | FloatPrim::DecEq
            | FloatPrim::IeeeEq
            | FloatPrim::IeeeLt
            | FloatPrim::IeeeLe
            | FloatPrim::Compare => 2,
            _ => 1,
        }
    }
}

/// The `Float` definitions with natives in the runtimes only, as for
/// [`TEXT_NATIVES`].
const FLOAT_NATIVES: &[(Builtin, FloatPrim, &str)] = &[
    (
        Builtin::FloatIeeeEq,
        FloatPrim::IeeeEq,
        "6a3570208df3d0e9f57218bc99e683ccfffc3fc1e6912d063b9073a0d980c8d1",
    ),
    (
        Builtin::FloatCompare,
        FloatPrim::Compare,
        "c740d4004978dba3b37fe8fd6ff190347137680809519e8d993301e4b5c18d27",
    ),
];

/// Matches each runtime-only float native with the definition it replaces,
/// by content hash.
pub fn bind_float_natives(g: &Globals) -> Result<Vec<NativeBinding<FloatPrim>>, ResourceError> {
    bind_natives(g, FLOAT_NATIVES)
}

/// The library's `Float`, if its file is loaded and it is the declaration
/// the native double was written for: the kernel binds it only then, by
/// content hash (`stitchwort_core::float::FLOAT_DATA_HASH`).
pub fn float_data(g: &Globals) -> Option<DataId> {
    g.builtins.float.data
}

/// Which native representations and operations apply to a program: the
/// prelude's `Nat`, `Int` and `Text` (each only if it's the declaration its
/// representation was written for), and the operations bound to their
/// definitions. The switches say whether a backend wants native text and
/// integers at all (the JS backend turns them off for differential tests).
pub struct Representation {
    /// The prelude's `Nat`, if a number is native.
    pub nat: Option<DataId>,
    /// The prelude's `Text`, if a text is a native string.
    pub text: Option<DataId>,
    /// The prelude's text operations with native implementations, and which.
    pub text_natives: HashMap<DefId, TextNative>,
    /// The prelude's `Int`, if an integer is a native number.
    pub int: Option<DataId>,
    /// The prelude's integer operations with native implementations, and
    /// which.
    pub int_natives: HashMap<DefId, IntNative>,
    /// The library's `Float`, if it is loaded: a `Float` is then a native
    /// double. (It has no fallback representation: the kernel accepts only
    /// the declaration it was written for.)
    pub float: Option<DataId>,
    /// The `Float` operations with native implementations, and which.
    pub float_natives: HashMap<DefId, FloatPrim>,
}

impl Representation {
    /// What applies, with native text and integers wanted or not.
    pub fn new(
        g: &Globals,
        native_text: bool,
        native_int: bool,
    ) -> Result<Representation, ResourceError> {
        let text = text_data(g).filter(|_| native_text);
        let text_natives = if text.is_some() {
            bind_text_natives(g)?
                .into_iter()
                .filter(|b| b.bound)
                .filter_map(|b| Some((b.id?, b.native)))
                .collect()
        } else {
            HashMap::new()
        };
        // The natives assume the native representation, so they're used
        // only with it, and it only for the `Int` it was written for.
        let int = int_data(g).filter(|_| native_int);
        let int_natives = if int.is_some() {
            bind_int(g)?
                .natives
                .into_iter()
                .filter(|b| b.bound && (text.is_some() || !b.native.uses_text()))
                .filter_map(|b| Some((b.id?, b.native)))
                .collect()
        } else {
            HashMap::new()
        };
        let float = float_data(g);
        let mut float_natives = HashMap::new();
        if float.is_some() {
            use stitchwort_core::float::{FloatNative, FloatOp};
            for id in (0..g.defs.len()).map(DefId) {
                let prim = match (g.builtins.float_primitive(id), g.builtins.float_native(id)) {
                    (Some(FloatOp::Add), _) => FloatPrim::Add,
                    (Some(FloatOp::Sub), _) => FloatPrim::Sub,
                    (Some(FloatOp::Mul), _) => FloatPrim::Mul,
                    (Some(FloatOp::Div), _) => FloatPrim::Div,
                    (Some(FloatOp::Rem), _) => FloatPrim::Rem,
                    (Some(FloatOp::Floor), _) => FloatPrim::Floor,
                    (Some(FloatOp::Ceil), _) => FloatPrim::Ceil,
                    (Some(FloatOp::Trunc), _) => FloatPrim::Trunc,
                    (Some(FloatOp::Round), _) => FloatPrim::Round,
                    (Some(FloatOp::OfInt), _) => FloatPrim::OfInt,
                    (Some(FloatOp::OfNat), _) => FloatPrim::OfNat,
                    (Some(FloatOp::ToText), _) => FloatPrim::ToText,
                    (_, Some(FloatNative::Neg)) => FloatPrim::Neg,
                    (_, Some(FloatNative::Abs)) => FloatPrim::Abs,
                    (_, Some(FloatNative::IsNaN)) => FloatPrim::IsNaN,
                    (_, Some(FloatNative::DecEq)) => FloatPrim::DecEq,
                    (_, Some(FloatNative::IsFinite)) => FloatPrim::IsFinite,
                    (_, Some(FloatNative::IeeeLt)) => FloatPrim::IeeeLt,
                    (_, Some(FloatNative::IeeeLe)) => FloatPrim::IeeeLe,
                    (_, Some(FloatNative::ToInt)) => FloatPrim::ToInt,
                    _ => continue,
                };
                float_natives.insert(id, prim);
            }
            for b in bind_float_natives(g)? {
                if let (true, Some(id)) = (b.bound, b.id) {
                    float_natives.insert(id, b.native);
                }
            }
        }
        Ok(Representation {
            nat: nat_data(g),
            text,
            text_natives,
            int,
            int_natives,
            float,
            float_natives,
        })
    }

    /// Which kernel-native implementation applies to `id`, if any: the
    /// number natives assume the native representation, so they apply only
    /// with it ([`nat_data`]).
    pub fn kernel_native(&self, g: &Globals, id: DefId) -> Option<native::Native> {
        self.nat.and(g.builtins.native(id))
    }

    /// Whether `id` has a native implementation of any kind.
    pub fn is_native(&self, g: &Globals, id: DefId) -> bool {
        self.kernel_native(g, id).is_some()
            || self.text_natives.contains_key(&id)
            || self.int_natives.contains_key(&id)
            || self.float_natives.contains_key(&id)
    }
}
