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

use stitchwort_core::collections::HashMap;

use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::native;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Ev, Limits, ResourceError};

/// A prelude text operation with a native implementation, where a `Text` is
/// a native string (in JS, with the backend's `Options::native_text`). Like the
/// number natives, these are trusted, and tested against the definitions
/// they replace (`crates/cli/tests/extraction/extract.rs`). Each works on Unicode scalar
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
    TextTake,
    TextDrop,
    TextContains,
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
        "284fe1fdbf1242de782805124c54d53eba56704a0ca842756f125ce7fb2ab554",
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
        "77694b50ab45fa909aa27f9cd6f8f9cf34d4047d38e2795f873963058f31dcd8",
    ),
    (
        Builtin::TextTrim,
        TextNative::TextTrim,
        "579048d18336dd30785965eb0c89f7804d796003518cefd73a5b808c47718574",
    ),
    (
        Builtin::TextTake,
        TextNative::TextTake,
        "8e0c767509cf080610e5ee09a9adb58a495aa51c7c523b24816ec820cd6c6c5f",
    ),
    (
        Builtin::TextDrop,
        TextNative::TextDrop,
        "c8270e372e015913632a3d7dcd1c2d58fe8976a771df1b9f4e7fdeb65804ff3b",
    ),
    (
        Builtin::TextContains,
        TextNative::TextContains,
        "707c59552f24471e93dc9d7534715a1e8cc783e3b435bab15264525cc9d2506d",
    ),
    (
        Builtin::TextSplit,
        TextNative::TextSplit,
        "88d29cee91b0d3b4dc3d2fcc242f9bfa0826138b6098c4b9e44a32d50cf8e093",
    ),
    (
        Builtin::TextJoin,
        TextNative::TextJoin,
        "4df47c8c59ae01257971b9a5579540a13c11820e5d9cf2e4f5bec2593c597da1",
    ),
    (
        Builtin::NatToText,
        TextNative::NatToText,
        "158940e00fe15b728004ba2320151434757b5f5ae3173511855cf86106b2645c",
    ),
    (
        Builtin::TextToNat,
        TextNative::TextToNat,
        "1d1e755952df72b7a810de03191f63919a7f0ba30e607cd26db7968a48846b73",
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
    g: &Ev,
    table: &[(Builtin, N, &str)],
) -> Result<Vec<NativeBinding<N>>, ResourceError> {
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    table
        .iter()
        .map(|&(builtin, native, expected)| {
            // Natives are mostly library built-ins, whose file may not have
            // loaded: then the program has no such definition to replace.
            let id = g.env.registry().loaded_def(builtin);
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
pub fn bind_text_natives(g: &Ev) -> Result<Vec<TextBinding>, ResourceError> {
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
pub fn bind_int(g: &Ev) -> Result<IntBinding, ResourceError> {
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let data = g.env.registry().data(Builtin::Int);
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
pub fn int_data(g: &Ev) -> Option<DataId> {
    let d = g.env.registry().data(Builtin::Int)?;
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Int` ran out of resources")?;
    (hash.hex() == INT_DATA_HASH).then_some(d)
}

/// The prelude's `Nat`, if the `bigint` representation applies to it
/// ([`NAT_DATA_HASH`]). Hashing a checked data type takes a few stack frames,
/// and the hash is remembered.
pub fn nat_data(g: &Ev) -> Option<DataId> {
    let d = g.env.registry().data(Builtin::Nat)?;
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Nat` ran out of resources")?;
    (hash.hex() == NAT_DATA_HASH).then_some(d)
}

/// The prelude's `Text`, if the JS string representation applies to it
/// ([`TEXT_DATA_HASH`]). Hashing a checked data type takes a few stack
/// frames, and the hash is remembered.
pub fn text_data(g: &Ev) -> Option<DataId> {
    let d = g.env.registry().data(Builtin::Text)?;
    let _op = g
        .machine
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
pub fn safe_nat_data(g: &Ev) -> Option<DataId> {
    let d = g.env.registry().loaded_data(Builtin::SafeNat)?;
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `SafeNat` ran out of resources")?;
    (hash.hex() == SAFE_NAT_HASH).then_some(d)
}

/// The library's `SafeInt`, if its file is loaded and the `number` codec
/// applies to it ([`SAFE_INT_HASH`]).
pub fn safe_int_data(g: &Ev) -> Option<DataId> {
    let d = g.env.registry().loaded_data(Builtin::SafeInt)?;
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `SafeInt` ran out of resources")?;
    (hash.hex() == SAFE_INT_HASH).then_some(d)
}

/// A prelude integer operation with a native implementation, where an `Int`
/// is a native number (in JS a `bigint`, with the backend's
/// `Options::native_int`). Like the
/// number and text natives, these are trusted, and tested against the
/// definitions they replace (`crates/cli/tests/extraction/extract.rs`). A division's
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
        "4ca08f568e7446cbd914942d9506f0ce13201e32eae270f0a65abfae040e2f97",
    ),
    (
        Builtin::IntMod,
        IntNative::IntMod,
        "a7c50c3c72bd16a6a4b4e69b2da0699b4d5bdfc2407c84dbf238c541d6c69b18",
    ),
    (
        Builtin::IntTDiv,
        IntNative::IntTDiv,
        "52db60c4f09b0da44a2f328f587e3895e5784e9d0786aa577342803e61fd0101",
    ),
    (
        Builtin::IntTMod,
        IntNative::IntTMod,
        "d4a4b79f52653e3658ea39c93da6e368d8bacea46b841873615f94afc3827758",
    ),
    (
        Builtin::IntFDiv,
        IntNative::IntFDiv,
        "85659c0fb0e8d5fa549d4e61eae05ce32564cd2d3258cbf0018397d3d8792e65",
    ),
    (
        Builtin::IntFMod,
        IntNative::IntFMod,
        "ae8240304ae2a2199043fb241344a698988f8ab2d4965d0aa2527aec0b7e62a5",
    ),
    (
        Builtin::IntModNat,
        IntNative::IntModNat,
        "020c47367b21ab954fe1b4d21089307f262248fefa0ec67ce37d39a24262dc16",
    ),
    (
        Builtin::DecEqInt,
        IntNative::DecEqInt,
        "2d47ac360bceb3e58f4c321d30391677d4db21e55adb37abde559ea2c9fb61b7",
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
        "502e9eee9f2cadbdc3ad81bc1d948cbe300f1a706f69670ae51d09192d7ede9b",
    ),
    (
        Builtin::TextToInt,
        IntNative::TextToInt,
        "153e329374c7dbb2292ae8e68aabc8affc9aa52bcc23ea59a208c1bfb1fab7d5",
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
    /// The total order's `<=` and `<` (`Float.leq`, `Float.less`).
    Leq,
    Less,
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
            | FloatPrim::Compare
            | FloatPrim::Leq
            | FloatPrim::Less => 2,
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
    (
        Builtin::FloatLeq,
        FloatPrim::Leq,
        "7687187777e2ed58f2858a7cd6770ced92ef87b9eb877ae6c3104a55af558fd0",
    ),
    (
        Builtin::FloatLess,
        FloatPrim::Less,
        "767cca38241182c31b60695919b8e178f29cf63f1e421f2c000e7d084f8da5dc",
    ),
];

/// Matches each runtime-only float native with the definition it replaces,
/// by content hash.
pub fn bind_float_natives(g: &Ev) -> Result<Vec<NativeBinding<FloatPrim>>, ResourceError> {
    bind_natives(g, FLOAT_NATIVES)
}

/// A `Fin` conversion that is the identity in the fast runtimes, where a
/// `Fin` is stored as the `Nat` it counts up to
/// ([`crate::erasure::nat_shape`]; docs/proposals/nat-shaped-types.md,
/// stage 2). Each runs as a function returning its number argument, which
/// the simplifier inlines at a direct call, so it costs no steps there and
/// one frame when called as a closure, instead of one frame per `FSucc`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinNative {
    /// `Fin.toNat i` is `i`.
    ToNat,
    /// `Fin.ofNatLt n i lt` is `i`: the bound is the erased proof's job.
    OfNatLt,
}

impl FinNative {
    /// Which of the definition's parameters (counting erased ones) is the
    /// number it returns: `i` in both `Fin.toNat [n] i` and
    /// `Fin.ofNatLt n i lt`.
    pub fn number_param(self) -> usize {
        match self {
            FinNative::ToNat | FinNative::OfNatLt => 1,
        }
    }
}

/// The `Fin` conversions with identity natives, as for [`TEXT_NATIVES`].
/// A definition's content hash covers `Fin` too, so a changed `Fin` unbinds
/// them as well as a changed definition.
const FIN_NATIVES: &[(Builtin, FinNative, &str)] = &[
    (
        Builtin::FinToNat,
        FinNative::ToNat,
        "106c7ba8a8ebfe6ef8cdd02c2b90caf68efb1c3e47ae2a0c0df35f8b11d0350c",
    ),
    (
        Builtin::FinOfNatLt,
        FinNative::OfNatLt,
        "eb62ae31e78cd162de92fcbe29736b46353a8ba13aedee582ce8d6fba638888a",
    ),
];

/// Matches each `Fin` native with the definition it replaces, by content
/// hash.
pub fn bind_fin_natives(g: &Ev) -> Result<Vec<NativeBinding<FinNative>>, ResourceError> {
    bind_natives(g, FIN_NATIVES)
}

/// The `Fin` natives that apply: those bound by hash, and only while `Fin`
/// is stored as a number. It isn't while rebuilds are checked
/// ([`crate::erasure::check_rebuilds`]), and an identity native given a
/// cell would return the cell.
pub fn fin_natives(g: &Ev) -> Result<HashMap<DefId, FinNative>, ResourceError> {
    let numbers = g
        .env
        .registry()
        .loaded_data(Builtin::Fin)
        .is_some_and(|d| crate::erasure::nat_shape(g, d).is_some());
    if !numbers {
        return Ok(HashMap::default());
    }
    Ok(bind_fin_natives(g)?
        .into_iter()
        .filter(|b| b.bound)
        .filter_map(|b| Some((b.id?, b.native)))
        .collect())
}

/// The library's `Float`, if its file is loaded and it is the declaration
/// the native double was written for: the kernel binds it only then, by
/// content hash (its pin in `stitchwort_core::pins`).
pub fn float_data(g: &Ev) -> Option<DataId> {
    g.env.builtins().float.data
}

/// Which native representations and operations apply to a program: the
/// prelude's `Nat`, `Int` and `Text` (each only if it's the declaration its
/// representation was written for), and the operations bound to their
/// definitions. The switches say whether a backend wants native text and
/// integers at all (the JS backend turns them off for differential tests).
/// Besides these, the fast runtime stores a type shaped like `Nat` (`Fin`,
/// say) as a `Nat` by its shape alone ([`crate::erasure::nat_shape`]), and a
/// record with one stored field as that field (D866).
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
        g: &Ev,
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
            HashMap::default()
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
            HashMap::default()
        };
        let float = float_data(g);
        let mut float_natives = HashMap::default();
        if float.is_some() {
            use stitchwort_core::float::{FloatNative, FloatOp};
            for id in (0..g.env.defs().len()).map(DefId) {
                let prim = match (
                    g.env.builtins().float_primitive(id),
                    g.env.builtins().float_native(id),
                ) {
                    (_, Some(FloatNative::Add)) => FloatPrim::Add,
                    (_, Some(FloatNative::Sub)) => FloatPrim::Sub,
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
    pub fn kernel_native(&self, g: &Ev, id: DefId) -> Option<native::Native> {
        self.nat.and(g.env.builtins().native(id))
    }

    /// Whether `id` has a native implementation of any kind.
    pub fn is_native(&self, g: &Ev, id: DefId) -> bool {
        self.kernel_native(g, id).is_some()
            || self.text_natives.contains_key(&id)
            || self.int_natives.contains_key(&id)
            || self.float_natives.contains_key(&id)
    }
}

/// An `Array` operation with a native implementation, where an array is one
/// buffer of values (`Value::Array`; docs/proposals/arrays.md §4.2). Like the
/// other natives these are trusted, and each computes what the definition it
/// replaces computes on the array's list: out of range, `get` is `None`,
/// `getOr` the fallback, and `set` leaves the array as it was. `FromList`
/// and `ToList` are the record's constructor and its `toList` field.
///
/// `Set`, `Push` and `Pop` take the array they change by value
/// ([`ArrayNative::consumes`]): when that was its last reference they change
/// the buffer in place, and otherwise copy it first, which the copy counter
/// counts (`crate::prims::array_copies`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArrayNative {
    FromList,
    ToList,
    Size,
    Get,
    GetOr,
    GetLt,
    Set,
    Push,
    Pop,
    Replicate,
}

impl ArrayNative {
    pub const ALL: [ArrayNative; 10] = [
        ArrayNative::FromList,
        ArrayNative::ToList,
        ArrayNative::Size,
        ArrayNative::Get,
        ArrayNative::GetOr,
        ArrayNative::GetLt,
        ArrayNative::Set,
        ArrayNative::Push,
        ArrayNative::Pop,
        ArrayNative::Replicate,
    ];

    /// How many runtime arguments it takes (`getLt`'s proof is erased).
    pub fn arity(self) -> u32 {
        match self {
            ArrayNative::FromList | ArrayNative::ToList | ArrayNative::Size | ArrayNative::Pop => 1,
            ArrayNative::Get | ArrayNative::GetLt | ArrayNative::Push | ArrayNative::Replicate => 2,
            ArrayNative::GetOr | ArrayNative::Set => 3,
        }
    }

    /// Whether it takes its first argument, the array, by value: the
    /// operations that change it.
    pub fn consumes(self) -> bool {
        matches!(
            self,
            ArrayNative::Set | ArrayNative::Push | ArrayNative::Pop
        )
    }
}

/// Each array native with a definition, the definition it replaces, and that
/// definition's content hash, as for [`TEXT_NATIVES`]. Unlike the text
/// natives they bind all or nothing ([`ArrayBinding::refusal`]): a lost
/// array native would turn an O(1) operation into an O(n) one through the
/// list, which is a hang rather than a slowdown (SW-1582).
const ARRAY_NATIVES: &[(Builtin, ArrayNative, &str)] = &[
    (
        Builtin::ArraySize,
        ArrayNative::Size,
        "3c39c99c9c13625e7958636ac8f2846c7d3602b3dbd12e6e8e5d7e52e103fb94",
    ),
    (
        Builtin::ArrayGet,
        ArrayNative::Get,
        "6b41677bb704884e48b9153595a88244908327ac613cf35208a76e34763fa144",
    ),
    (
        Builtin::ArrayGetOr,
        ArrayNative::GetOr,
        "a1655db7071885d0fb8053272beab0809f178440ee96eff1c45e81611a39e630",
    ),
    (
        Builtin::ArrayGetLt,
        ArrayNative::GetLt,
        "edc9d5e4c5a5b3fd6d411b565867354b854f2ab214f46b4d2bf0d2174d550aaf",
    ),
    (
        Builtin::ArraySet,
        ArrayNative::Set,
        "e3dc7603de1f7138400aa975330e9199a9ad73bd4c89499e5006d9b4b3ad821f",
    ),
    (
        Builtin::ArrayPush,
        ArrayNative::Push,
        "349967d17cfeca33d41dcafa57656c7721c395193224de9b71c5df74ac3455de",
    ),
    (
        Builtin::ArrayPop,
        ArrayNative::Pop,
        "f276faee627c6281c0a8eb3075a2cab912fb6a6f830da35f828a2d1c2bfbf74d",
    ),
    (
        Builtin::ArrayReplicate,
        ArrayNative::Replicate,
        "0be1b473fe95e3410fe7cb0cdf238c8e79f12107cb42d968ba308fde2c7163f5",
    ),
];

/// The content hash of the library's `Array` (std/Array/Array.sw), which the
/// buffer representation was written for: a record of one field, a `List`.
/// It and every entry of [`ARRAY_NATIVES`] apply together or not at all.
pub const ARRAY_DATA_HASH: &str =
    "d17cac33bd251d71f7d539b50a71d9b4577439afca590cb92b487577f91908c9";

/// Whether the buffer representation applies to the library's `Array`, and
/// to which of its definitions the natives apply.
pub struct ArrayBinding {
    /// The library's `Array`, if its file is loaded.
    pub data: Option<DataId>,
    /// Its content hash, in hex.
    pub hash: Option<String>,
    /// Whether it's the data type the representation was written for.
    pub bound: bool,
    pub natives: Vec<NativeBinding<ArrayNative>>,
}

impl ArrayBinding {
    /// The representation and natives, if the file is loaded and every one
    /// of them is bound.
    pub fn applies(&self) -> Option<(DataId, HashMap<DefId, ArrayNative>)> {
        let data = self.data?;
        if self.refusal().is_some() {
            return None;
        }
        let natives = self
            .natives
            .iter()
            .filter_map(|b| Some((b.id?, b.native)))
            .collect();
        Some((data, natives))
    }

    /// Why a program that loads `Array` can't run, if it can't: the data type
    /// or one of the natives isn't the declaration it was written for. A
    /// program that doesn't load the file is never refused.
    pub fn refusal(&self) -> Option<String> {
        self.data?;
        let mut stale: Vec<String> = Vec::new();
        if !self.bound {
            stale.push(format!(
                "`Array` ({})",
                self.hash.as_deref().unwrap_or("none")
            ));
        }
        for b in &self.natives {
            if !b.bound {
                stale.push(format!(
                    "`{}` ({})",
                    b.name,
                    b.hash.as_deref().unwrap_or("missing")
                ));
            }
        }
        (!stale.is_empty()).then(|| {
            format!(
                "the library's arrays aren't the declarations the runtime's array natives were \
                 written for: {}; check each native against the changed definition, then update \
                 its hash in crates/rt/src/natives.rs",
                stale.join(", ")
            )
        })
    }
}

/// Matches the buffer representation with the library's `Array`, and each
/// array native with the definition it replaces, by content hash.
pub fn bind_array(g: &Ev) -> Result<ArrayBinding, ResourceError> {
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let data = g.env.registry().loaded_data(Builtin::Array);
    let hash = match data {
        Some(d) => data_hash(g, d)?.map(|h| h.hex()),
        None => None,
    };
    Ok(ArrayBinding {
        data,
        bound: hash.as_deref() == Some(ARRAY_DATA_HASH),
        hash,
        natives: bind_natives(g, ARRAY_NATIVES)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binding(data: bool, bound: bool, native_bound: bool) -> ArrayBinding {
        ArrayBinding {
            data: data.then_some(DataId(0)),
            hash: Some("cafe".into()),
            bound,
            natives: vec![NativeBinding {
                name: "Array.set",
                native: ArrayNative::Set,
                id: Some(DefId(0)),
                hash: Some("beef".into()),
                bound: native_bound,
            }],
        }
    }

    /// All or nothing: one stale native refuses the program, naming it, and
    /// nothing applies; a program that doesn't load `Array` is never refused.
    #[test]
    fn arrays_bind_all_or_nothing() {
        let stale = binding(true, true, false);
        let why = stale.refusal().expect("refused");
        assert!(why.contains("`Array.set` (beef)"), "{why}");
        assert!(stale.applies().is_none());
        assert!(
            binding(true, false, true)
                .refusal()
                .expect("refused")
                .contains("`Array` (cafe)")
        );
        assert!(binding(false, false, false).refusal().is_none());
        let (_, natives) = binding(true, true, true).applies().expect("applies");
        assert_eq!(natives.get(&DefId(0)), Some(&ArrayNative::Set));
    }
}
