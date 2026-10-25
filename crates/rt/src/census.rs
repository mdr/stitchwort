//! The opcode census: which of the machine's instructions a program's
//! reachable code uses, and whether that code fits stage N1 of native
//! compilation (docs/proposals/native-compilation.md, section 4.6 and the N1
//! row of the stages table). A measurement tool; it doesn't change what the
//! machine does.
//!
//! **Islands.** The entry's *island* is the set of bodies reachable from it.
//! It fits N1 if every instruction in it is in the N1 subset
//! ([`n1_blocker`]). The walk follows:
//!
//! - direct edges: `Call`, `TailCall`, and `Global` of a constant (its body
//!   runs when first used);
//! - *creation* edges for indirect calls: wherever a function value is made
//!   (`Closure` makes a lambda, `Pap` and `Global` of a function make a
//!   global function), the target body is counted as reached.
//!
//! `Apply`/`TailApply` have no static target. Rather than mark the island
//! impure for that alone, the census uses the cheap closure-creation
//! analysis: a function value can only come from a creation site, and the
//! creation sites in reached code are all counted, so every body an `Apply`
//! could call is in the island (the over-approximation also counts bodies
//! whose value is never applied). Function values that come from outside
//! (host callbacks, the effect runtime's natives) pass through `Prim`
//! instructions, which are blockers anyway. `Apply` itself is not in the N1
//! subset, so any island with one is blocked; the creation edges make the
//! census say what *else* blocks such an island, which is what matters for
//! deciding what to add next.

use std::collections::BTreeMap;

use crate::code::{Code, Image, Instr, compile};
use crate::ir::{GlobalKind, PrimOp, Program};

/// The kind of an instruction, by name (`Call`, `Prim`, ...).
pub fn instr_name(instr: &Instr) -> &'static str {
    match instr {
        Instr::Move { .. } => "Move",
        Instr::Take { .. } => "Take",
        Instr::Drop { .. } => "Drop",
        Instr::Const { .. } => "Const",
        Instr::Captured { .. } => "Captured",
        Instr::Global { .. } => "Global",
        Instr::Call { .. } => "Call",
        Instr::TailCall { .. } => "TailCall",
        Instr::Prim { .. } => "Prim",
        Instr::TailPrim { .. } => "TailPrim",
        Instr::Pap { .. } => "Pap",
        Instr::Apply { .. } => "Apply",
        Instr::TailApply { .. } => "TailApply",
        Instr::Closure { .. } => "Closure",
        Instr::Ctor { .. } => "Ctor",
        Instr::CtorReuse { .. } => "CtorReuse",
        Instr::Switch { .. } => "Switch",
        Instr::Field { .. } => "Field",
        Instr::Unpack { .. } => "Unpack",
        Instr::DropReuse { .. } => "DropReuse",
        Instr::NatCase { .. } => "NatCase",
        Instr::NatPred { .. } => "NatPred",
        Instr::IntCase { .. } => "IntCase",
        Instr::IntOfNat { .. } => "IntOfNat",
        Instr::IntNegSucc { .. } => "IntNegSucc",
        Instr::TextChars { .. } => "TextChars",
        Instr::NumSwitch { .. } => "NumSwitch",
        Instr::JumpIfFalse { .. } => "JumpIfFalse",
        Instr::Test { .. } => "Test",
        Instr::Jump { .. } => "Jump",
        Instr::Return { .. } => "Return",
        Instr::Unreachable => "Unreachable",
    }
}

/// The N1 subset, from the N1 row of the stages table: `Move`, `Take`,
/// `Drop`, `Const`, `Call`, `TailCall`, `Return`, `Switch`, `Field`,
/// `Unpack`, `Ctor`, `CtorReuse`, `Test`, `JumpIfFalse`, `Jump`, and `Prim`
/// of the `Nat` operations (`Test` of a `Nat` comparison), plus the `Nat`
/// match instructions `NatCase`, `NatPred` and `NumSwitch` (read from "`Nat`
/// fast paths"; remove them here to see the effect). Nothing else.
///
/// Returns `None` if `instr` is in the subset, otherwise the blocker's key:
/// the instruction's name, with the operation for a `Prim`, `TailPrim` or
/// `Test` (`Prim:Int(IntAdd)`), since those are separate decisions.
pub fn n1_blocker(instr: &Instr) -> Option<String> {
    match instr {
        Instr::Move { .. }
        | Instr::Take { .. }
        | Instr::Drop { .. }
        | Instr::Const { .. }
        // The `Nat` match instructions: the row's "`Nat` fast paths" (a
        // `Nat` pattern match lowers to them, and `micro_call`/`micro_tail`
        // need them), so counted in.
        | Instr::NatCase { .. }
        | Instr::NatPred { .. }
        | Instr::NumSwitch { .. }
        | Instr::Call { .. }
        | Instr::TailCall { .. }
        | Instr::Return { .. }
        | Instr::Switch { .. }
        | Instr::Field { .. }
        | Instr::Unpack { .. }
        | Instr::Ctor { .. }
        | Instr::CtorReuse { .. }
        | Instr::JumpIfFalse { .. }
        | Instr::Jump { .. } => None,
        Instr::Prim { op, .. } | Instr::Test { op, .. } if matches!(op, PrimOp::Nat(_)) => None,
        Instr::Prim { op, .. } | Instr::Test { op, .. } | Instr::TailPrim { op, .. } => {
            Some(format!("{}:{op:?}", instr_name(instr)))
        }
        other => Some(instr_name(other).to_string()),
    }
}

/// One reachable body.
#[derive(Debug)]
pub struct BodyReport {
    /// The index in [`Image::codes`].
    pub code: u32,
    /// `Std.List.map`, `lambda #3`, `entry`.
    pub name: String,
    /// How many times each instruction kind occurs (names, as
    /// [`instr_name`]).
    pub instrs: BTreeMap<&'static str, usize>,
    /// The N1 blockers in it ([`n1_blocker`]) and how many times each occurs.
    pub blockers: BTreeMap<String, usize>,
}

/// The census of one program.
#[derive(Debug)]
pub struct Census {
    /// The bodies reachable from the entry, entry first.
    pub bodies: Vec<BodyReport>,
    /// Bodies in the whole image (reachable or not).
    pub image_bodies: usize,
}

impl Census {
    /// Every reachable instruction is in the N1 subset.
    pub fn fits_n1(&self) -> bool {
        self.bodies.iter().all(|b| b.blockers.is_empty())
    }

    /// The blockers over the island: for each, the number of occurrences and
    /// the number of bodies it occurs in.
    pub fn blockers(&self) -> BTreeMap<String, (usize, usize)> {
        let mut out: BTreeMap<String, (usize, usize)> = BTreeMap::new();
        for body in &self.bodies {
            for (key, n) in &body.blockers {
                let e = out.entry(key.clone()).or_default();
                e.0 += n;
                e.1 += 1;
            }
        }
        out
    }

    /// As [`Census::blockers`], by [`family`], each body counted once per
    /// family.
    pub fn family_blockers(&self) -> BTreeMap<String, (usize, usize)> {
        let mut out: BTreeMap<String, (usize, usize)> = BTreeMap::new();
        for body in &self.bodies {
            let mut per_body: BTreeMap<&str, usize> = BTreeMap::new();
            for (key, n) in &body.blockers {
                *per_body.entry(family(key)).or_default() += n;
            }
            for (fam, n) in per_body {
                let e = out.entry(fam.to_string()).or_default();
                e.0 += n;
                e.1 += 1;
            }
        }
        out
    }

    /// The blocker keys that, if they were the only ones the island had,
    /// would be the whole difference: the island's blocker set, when it has
    /// exactly one entry. Adding that instruction alone makes the island fit.
    pub fn sole_blocker(&self) -> Option<String> {
        let blockers = self.blockers();
        if blockers.len() == 1 {
            blockers.into_keys().next()
        } else {
            None
        }
    }

    /// Instruction kinds over the island: occurrences and bodies using it.
    pub fn instr_totals(&self) -> BTreeMap<&'static str, (usize, usize)> {
        let mut out: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();
        for body in &self.bodies {
            for (name, n) in &body.instrs {
                let e = out.entry(name).or_default();
                e.0 += n;
                e.1 += 1;
            }
        }
        out
    }
}

/// Compiles `program` as the machine does and takes the census of what its
/// entry reaches.
pub fn census(program: &Program) -> Census {
    census_image(program, &compile(program))
}

/// The census of an already compiled `program`, from its entry.
pub fn census_image(program: &Program, image: &Image) -> Census {
    census_from(program, image, image.entry_code)
}

/// The islands of the functions the entry body calls or makes: what a host
/// that starts a computation at a function (rather than at the entry's
/// glue, which builds the `Delay` the runner steps and so always uses the
/// `Delay` primitives) would run. One census per distinct body the entry
/// refers to directly.
pub fn callee_censuses(program: &Program, image: &Image) -> Vec<Census> {
    let mut targets = Vec::new();
    for instr in &image.codes[image.entry_code as usize].instrs {
        if let Some(t) = edge(image, instr)
            && !targets.contains(&t)
        {
            targets.push(t);
        }
    }
    targets
        .into_iter()
        .map(|t| census_from(program, image, t))
        .collect()
}

/// For each body of `census` whose own island fits N1: its name and the
/// island's size, largest first. This is the pure code that would run native
/// if an invocation could start at any function (not only the entry), so it
/// says how much of a program is native-ready even when its entry is not.
pub fn fitting_islands(image: &Image, census: &Census) -> Vec<(String, usize)> {
    fitting_islands_with(image, census, &[])
}

/// A blocker's family: its key up to the operation (`Prim:Text`,
/// `Apply`). Adding an instruction to N1 means adding a family, or, for the
/// `Prim`s, a family's operations.
pub fn family(key: &str) -> &str {
    key.split('(').next().unwrap_or(key)
}

/// As [`fitting_islands`], if the blocker families `extra` were also in the
/// N1 subset.
pub fn fitting_islands_with(
    image: &Image,
    census: &Census,
    extra: &[String],
) -> Vec<(String, usize)> {
    let blocked: std::collections::HashSet<u32> = census
        .bodies
        .iter()
        .filter(|b| {
            b.blockers
                .keys()
                .any(|k| !extra.iter().any(|e| e == family(k)))
        })
        .map(|b| b.code)
        .collect();
    let mut out: Vec<(String, usize)> = census
        .bodies
        .iter()
        .filter_map(|b| {
            let island = island(image, b.code);
            island
                .iter()
                .all(|c| !blocked.contains(c))
                .then(|| (b.name.clone(), island.len()))
        })
        .collect();
    out.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    out
}

/// What adding blocker families to N1 would buy, greedily: the family that
/// makes the most bodies' islands fit, then the next given that one, and so
/// on until nothing more fits. Each step is the family, the number of bodies
/// whose island fits after adding it, and whether the whole entry island
/// does.
pub fn greedy_additions(image: &Image, census: &Census) -> Vec<(String, usize, bool)> {
    let mut families: Vec<String> = census
        .blockers()
        .keys()
        .map(|k| family(k).to_string())
        .collect();
    families.sort();
    families.dedup();
    let mut chosen: Vec<String> = Vec::new();
    let mut steps = Vec::new();
    let mut best_so_far = fitting_islands_with(image, census, &chosen).len();
    loop {
        let mut best: Option<(String, usize)> = None;
        for f in &families {
            if chosen.contains(f) {
                continue;
            }
            let mut trial = chosen.clone();
            trial.push(f.clone());
            let n = fitting_islands_with(image, census, &trial).len();
            if n > best.as_ref().map_or(best_so_far, |b| b.1) {
                best = Some((f.clone(), n));
            }
        }
        let Some((f, n)) = best else { break };
        chosen.push(f.clone());
        best_so_far = n;
        let entry_fits = census.bodies.iter().all(|b| {
            b.blockers
                .keys()
                .all(|k| chosen.iter().any(|e| e == family(k)))
        });
        steps.push((f, n, entry_fits));
    }
    steps
}

/// The body an instruction refers to directly, if any: a call, or the
/// creation of a function value (see the module comment).
fn edge(image: &Image, instr: &Instr) -> Option<u32> {
    match instr {
        Instr::Call { g, .. }
        | Instr::TailCall { g, .. }
        | Instr::Global { g, .. }
        | Instr::Pap { g, .. } => image.global_code[*g as usize],
        Instr::Closure { lambda, .. } => Some(image.lambda_code[*lambda as usize]),
        _ => None,
    }
}

/// The bodies reachable from `root`, `root` included.
fn island(image: &Image, root: u32) -> Vec<u32> {
    let mut seen = vec![false; image.codes.len()];
    let mut order = Vec::new();
    let mut stack = vec![root];
    seen[root as usize] = true;
    while let Some(code) = stack.pop() {
        order.push(code);
        for instr in &image.codes[code as usize].instrs {
            if let Some(t) = edge(image, instr)
                && !seen[t as usize]
            {
                seen[t as usize] = true;
                stack.push(t);
            }
        }
    }
    order
}

/// The census of the island of body `root`.
pub fn census_from(program: &Program, image: &Image, root: u32) -> Census {
    let names = body_names(program, image);
    let mut order = island(image, root);
    // The root first, then by index, so the report is stable.
    order.sort_by_key(|c| (*c != root, *c));
    let bodies = order
        .into_iter()
        .map(|code| {
            report(
                code,
                &image.codes[code as usize],
                names[code as usize].clone(),
            )
        })
        .collect();
    Census {
        bodies,
        image_bodies: image.codes.len(),
    }
}

fn report(code: u32, body: &Code, name: String) -> BodyReport {
    let mut instrs = BTreeMap::new();
    let mut blockers = BTreeMap::new();
    for instr in &body.instrs {
        *instrs.entry(instr_name(instr)).or_default() += 1;
        if let Some(key) = n1_blocker(instr) {
            *blockers.entry(key).or_default() += 1;
        }
    }
    BodyReport {
        code,
        name,
        instrs,
        blockers,
    }
}

/// A name for each body of the image.
fn body_names(program: &Program, image: &Image) -> Vec<String> {
    let mut names = vec![String::new(); image.codes.len()];
    for (g, code) in image.global_code.iter().enumerate() {
        if let Some(code) = code {
            let global = &program.globals[g];
            let kind = match global.kind {
                GlobalKind::Constant { .. } => " (constant)",
                _ => "",
            };
            names[*code as usize] = format!("{}{kind}", global.name);
        }
    }
    for (l, code) in image.lambda_code.iter().enumerate() {
        names[*code as usize] = format!("lambda #{l}");
    }
    names[image.entry_code as usize] = "entry".to_string();
    names
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::Ops;

    #[test]
    fn subset_accepts_calls_and_blocks_apply() {
        let ok = Instr::Call {
            dst: 0,
            g: 0,
            args: Ops { start: 0, len: 0 },
        };
        assert_eq!(n1_blocker(&ok), None);
        let apply = Instr::Apply {
            dst: 0,
            f: 0,
            args: Ops { start: 0, len: 0 },
        };
        assert_eq!(n1_blocker(&apply).as_deref(), Some("Apply"));
        assert_eq!(
            n1_blocker(&Instr::Unreachable).as_deref(),
            Some("Unreachable")
        );
    }
}
