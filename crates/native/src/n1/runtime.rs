//! Stage NO2 of docs/proposals/native-only.md: the effect runtime's run
//! loop and eager resumptions as *runtime bodies*, Cranelift IR in the
//! `tail` convention like program bodies, so that the machine doesn't run
//! them for native code.
//!
//! - `rt_loop` is the machine's `eff_run` (and `eff_call`): a loop over the
//!   computation, each iteration a step (counted as the machine counts it),
//!   whose leaf `abi::sw_eff_step` takes the computation apart and says
//!   what to do. A `Done` with a continuation pending is an ordinary call of
//!   the continuation, and the loop goes on with its result: what the
//!   machine keeps in a `Ret::Eff` (the handler, the pending list) lives in
//!   this frame instead. A fold's `done x` and `call o k` are tail calls.
//! - `rt_resume` is the machine's `resume` for an eager resumption: the
//!   rest of the computation (after a `translate`'s `reply`) called, then
//!   `rt_loop` from its result, as a tail call.
//!
//! Neither pushes a frame or counts one; their calls count a step and a
//! frame each as the machine's `apply` does, directly for a global function
//! or a closure taking that many (the site's cache, as `Apply`'s), or
//! through the apply stub (`apply{n}`). Their leaves do the machine's
//! clones and drops in its order, so the allocation trace and the effect
//! counts are the machine's.
//!
//! **Error exits.** A call that fails gives up what this frame holds for
//! it (the handler, the pending list, a `translate`'s `rest` or `k`) to the
//! unwind log, joined to the group of the callee frame that just left, as
//! the machine keeps those in that frame's `Ret` (`abi::sw_unwind`'s mode
//! 3, `abi::sw_unwind_handler`); if no frame has left (out of steps or
//! frames before the call), they're dropped at once, as the machine's `push`
//! drops the `Ret` it never pushed. A callee's tail request is performed
//! here, as a body performs one.
//!
//! **A frame's closure.** Reached from a `TailPrim` (the loop) or a tail
//! apply (a resumption), the body is given the leaving frame's closure
//! (`env`, 0 for none), which the machine drops once the native has begun:
//! at the first call or return.

use std::collections::BTreeMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    self, AbiParam, FuncRef, InstBuilder, StackSlot, StackSlotData, StackSlotKind, TrapCode,
    Value as IrValue, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, Switch, Variable};
use cranelift_module::{FuncId, Module};
use stitchwort_rt::native_abi::{
    self as abi, Context, FUN_KEY_MASK, OUT_OF_FRAMES, OUT_OF_STEPS, RC_VALUE_AT, TAG_FUN,
    TAIL_REQUEST, Tables, VALUE_SIZE,
};

use super::{Helpers, Options, drop_fun, fixed, flags, steps_in, steps_out, value_signature};

/// The runtime bodies, declared.
#[derive(Clone, Copy)]
pub(crate) struct Runtime {
    pub(crate) run_loop: FuncId,
    pub(crate) resume: FuncId,
}

/// `rt_loop`'s signature: the context, the frames pending (the caller's:
/// it has no frame of its own), the computation and the pending list
/// (three words each, moved in), the handler's word and a leaving frame's
/// closure (0 for none), both owned; returning three words.
pub(crate) fn loop_signature(pointer: ir::Type) -> ir::Signature {
    let mut signature = ir::Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    for _ in 0..6 {
        signature.params.push(AbiParam::new(types::I64));
    }
    signature.params.push(AbiParam::new(types::I64));
    signature.params.push(AbiParam::new(pointer));
    for _ in 0..3 {
        signature.returns.push(AbiParam::new(types::I64));
    }
    signature
}

/// `rt_resume`'s signature: the context, the frames pending (the
/// caller's), the value resumed with (three words), the resumption's word
/// and a leaving frame's closure (0 for none), all owned; returning three
/// words.
pub(crate) fn resume_signature(pointer: ir::Type) -> ir::Signature {
    let mut signature = ir::Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    for _ in 0..3 {
        signature.params.push(AbiParam::new(types::I64));
    }
    signature.params.push(AbiParam::new(types::I64));
    signature.params.push(AbiParam::new(pointer));
    for _ in 0..3 {
        signature.returns.push(AbiParam::new(types::I64));
    }
    signature
}

/// What a runtime body holds while it calls something, to give up if the
/// call fails.
#[derive(Clone, Copy)]
enum Hold {
    /// A handler's word.
    Handler(Variable),
    /// A value in a stack slot.
    Value(StackSlot),
    /// A function value's word, or 0.
    Fun(Variable),
}

type Words = [IrValue; 3];

/// A runtime body being built.
struct Rt<'a, 'b> {
    b: &'b mut FunctionBuilder<'a>,
    module: &'b mut dyn Module,
    helpers: &'b Helpers,
    apply_any: &'b BTreeMap<u32, FuncId>,
    /// The `Apply` sites compiled so far (each has a cache in the tables).
    caches: &'b mut u32,
    pointer: ir::Type,
    options: Options,
    refs: BTreeMap<FuncId, FuncRef>,
    ctx: IrValue,
    frames: IrValue,
    /// Room for a function value (an apply's cache miss), or a performed
    /// tail request's value.
    scratch: StackSlot,
}

impl Rt<'_, '_> {
    fn fref(&mut self, id: FuncId) -> FuncRef {
        if let Some(r) = self.refs.get(&id) {
            return *r;
        }
        let r = self.module.declare_func_in_func(id, self.b.func);
        self.refs.insert(id, r);
        r
    }

    fn call(&mut self, id: FuncId, args: &[IrValue]) -> Vec<IrValue> {
        let f = self.fref(id);
        let call = self.b.ins().call(f, args);
        self.b.inst_results(call).to_vec()
    }

    fn iconst(&mut self, n: u64) -> IrValue {
        self.b.ins().iconst(types::I64, n as i64)
    }

    fn slot(&mut self, values: usize) -> StackSlot {
        self.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (values * VALUE_SIZE) as u32,
            3,
        ))
    }

    fn addr(&mut self, slot: StackSlot, value: usize) -> IrValue {
        self.b
            .ins()
            .stack_addr(self.pointer, slot, (value * VALUE_SIZE) as i32)
    }

    fn store(&mut self, slot: StackSlot, value: usize, v: Words) {
        let at = self.addr(slot, value);
        for (w, word) in v.iter().enumerate() {
            self.b.ins().store(flags(), *word, at, (w * 8) as i32);
        }
    }

    fn load(&mut self, slot: StackSlot, value: usize) -> Words {
        let at = self.addr(slot, value);
        std::array::from_fn(|w| self.b.ins().load(types::I64, flags(), at, (w * 8) as i32))
    }

    /// Drops a value this body owns (through the runtime, which counts it
    /// as the trace needs; only on the ways out of an error).
    fn drop_value(&mut self, v: Words) {
        self.call(self.helpers.drop_words, &v);
    }

    /// Drops the function value whose word the variable holds, if any, and
    /// clears the variable.
    fn drop_fun_var(&mut self, var: Variable) {
        let word = self.b.use_var(var);
        let dropping = self.b.create_block();
        let after = self.b.create_block();
        self.b.ins().brif(word, dropping, &[], after, &[]);
        self.b.switch_to_block(dropping);
        let drop_words = self.fref(self.helpers.drop_words);
        drop_fun(self.b, drop_words, word);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
        let zero = self.iconst(0);
        self.b.def_var(var, zero);
    }

    /// Gives up what the body holds, on an error exit (the module comment).
    fn release(&mut self, held: &[Hold]) {
        for hold in held {
            match *hold {
                Hold::Handler(var) => {
                    let word = self.b.use_var(var);
                    self.call(self.helpers.unwind_handler, &[self.ctx, word]);
                }
                Hold::Value(slot) => {
                    let at = self.addr(slot, 0);
                    let one = self.iconst(1);
                    let join = self.iconst(3);
                    self.call(self.helpers.unwind, &[self.ctx, at, one, join]);
                }
                Hold::Fun(var) => self.drop_fun_var(var),
            }
        }
    }

    /// Returns, after an error.
    fn leave(&mut self) {
        let zero = self.iconst(0);
        self.b.ins().return_(&[zero, zero, zero]);
    }

    /// A step, as the machine's `enter_frame` counts one: to `fail` if none
    /// is left.
    fn count_step(&mut self, fail: ir::Block) {
        let left = self.b.ins().get_pinned_reg(types::I64);
        let none_left = self.b.ins().icmp_imm_u(IntCC::Equal, left, 0);
        let out = self.b.create_block();
        let counted = self.b.create_block();
        self.b.ins().brif(none_left, out, &[], counted, &[]);
        self.b.switch_to_block(out);
        self.b.set_cold_block(out);
        // One step over the limit, as the machine counts it.
        let over = self.iconst(u64::MAX);
        self.b.ins().set_pinned_reg(over);
        let error = self.iconst(OUT_OF_STEPS);
        self.b
            .ins()
            .store(flags(), error, self.ctx, Context::ERROR_AT);
        self.b.ins().jump(fail, &[]);
        self.b.switch_to_block(counted);
        let fewer = self.b.ins().iadd_imm_s(left, -1);
        self.b.ins().set_pinned_reg(fewer);
    }

    /// A frame about to be pushed, as the machine's `enter_frame` checks
    /// it: to `fail` if as many are pending as the limit allows (or at the
    /// stack's safety margin).
    fn check_frame(&mut self, fail: ir::Block) {
        let limit = self
            .b
            .ins()
            .load(types::I64, flags(), self.ctx, Context::FRAME_LIMIT_AT);
        let mut over = self
            .b
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, self.frames, limit);
        if self.options.stack_size.is_some() {
            let sp = self.b.ins().get_stack_pointer(self.pointer);
            let floor = self
                .b
                .ins()
                .load(types::I64, flags(), self.ctx, Context::STACK_LIMIT_AT);
            let low = self.b.ins().icmp(IntCC::UnsignedLessThan, sp, floor);
            over = self.b.ins().bor(over, low);
        }
        let out = self.b.create_block();
        let fine = self.b.create_block();
        self.b.ins().brif(over, out, &[], fine, &[]);
        self.b.switch_to_block(out);
        self.b.set_cold_block(out);
        let error = self.iconst(OUT_OF_FRAMES);
        self.b
            .ins()
            .store(flags(), error, self.ctx, Context::ERROR_AT);
        self.b.ins().jump(fail, &[]);
        self.b.switch_to_block(fine);
    }

    /// What `Apply` of `fv` to `n` arguments calls directly (a global
    /// function or a closure taking `n`: the machine's `exact`), or 0: a new
    /// `Apply` site's cache, as a body's (`Gen::apply_target_of`).
    fn target_of(&mut self, fv: Words, n: u32) -> IrValue {
        let offset = i32::try_from(*self.caches as usize * size_of::<abi::ApplyCache>())
            .expect("the caches fit an offset");
        *self.caches += 1;
        let tables = self
            .b
            .ins()
            .load(self.pointer, fixed(), self.ctx, Context::TABLES_AT);
        let caches = self
            .b
            .ins()
            .load(self.pointer, fixed(), tables, Tables::CACHES_AT);
        let tag = self.b.ins().band_imm_u(fv[0], 0xff);
        let is_fun = self
            .b
            .ins()
            .icmp_imm_u(IntCC::Equal, tag, i64::from(TAG_FUN));
        let check = self.b.create_block();
        let cached = self.b.create_block();
        let miss = self.b.create_block();
        let after = self.b.create_block();
        self.b.append_block_param(after, self.pointer);
        self.b.ins().brif(is_fun, check, &[], miss, &[]);
        self.b.switch_to_block(check);
        let first = self.b.ins().load(types::I64, flags(), fv[1], RC_VALUE_AT);
        let mine = self.b.ins().band_imm_s(first, FUN_KEY_MASK as i64);
        let key = self.b.ins().load(
            types::I64,
            flags(),
            caches,
            offset + abi::ApplyCache::KEY_AT,
        );
        let hit = self.b.ins().icmp(IntCC::Equal, key, mine);
        self.b.ins().brif(hit, cached, &[], miss, &[]);
        self.b.switch_to_block(cached);
        let code = self.b.ins().load(
            self.pointer,
            flags(),
            caches,
            offset + abi::ApplyCache::CODE_AT,
        );
        self.b.ins().jump(after, &[code.into()]);
        self.b.switch_to_block(miss);
        self.b.set_cold_block(miss);
        self.store(self.scratch, 0, fv);
        let at = self.addr(self.scratch, 0);
        let cache_at = self.b.ins().iadd_imm_s(caches, i64::from(offset));
        let n = self.iconst(u64::from(n));
        let target = self.call(self.helpers.apply_cached, &[self.ctx, at, n, cache_at])[0];
        self.b.ins().jump(after, &[target.into()]);
        self.b.switch_to_block(after);
        self.b.block_params(after)[0]
    }

    /// `fv args` (all moved in), not in a tail position, as the machine's
    /// `apply`: its value. `pre` (at most one function value's word) is
    /// dropped as the machine drops the function value its own `apply` was
    /// given: once the frame is counted before a direct call, or by the
    /// apply stub once it has taken `fv` apart; `env` (a leaving frame's
    /// closure) after it. On an error, `held` is given up and the body
    /// returns.
    fn apply(
        &mut self,
        fv: Words,
        args: &[Words],
        pre: &[Variable],
        env: Option<Variable>,
        held: &[Hold],
    ) -> Words {
        let n = args.len() as u32;
        let target = self.target_of(fv, n);
        let exact = self.b.create_block();
        let slow = self.b.create_block();
        let returned = self.b.create_block();
        for _ in 0..3 {
            self.b.append_block_param(returned, types::I64);
        }
        self.b.ins().brif(target, exact, &[], slow, &[]);

        // A global function or a closure taking `n`: a step and a frame,
        // then the call.
        self.b.switch_to_block(exact);
        let unready = self.b.create_block();
        self.count_step(unready);
        self.check_frame(unready);
        for var in pre {
            self.drop_fun_var(*var);
        }
        if let Some(var) = env {
            self.drop_fun_var(var);
        }
        let pushed = self.b.ins().iadd_imm_s(self.frames, 1);
        let mut call_args = vec![self.ctx, pushed];
        call_args.extend(args.iter().flatten());
        call_args.push(fv[1]);
        let signature = self.b.import_signature(value_signature(self.pointer, n));
        let call = self.b.ins().call_indirect(signature, target, &call_args);
        let r: Vec<ir::BlockArg> = self
            .b
            .inst_results(call)
            .iter()
            .map(|x| (*x).into())
            .collect();
        self.b.ins().jump(returned, &r);

        // Anything else: the machine's eval/apply, in the stub.
        self.b.switch_to_block(slow);
        let drops = match pre {
            [] => self.b.ins().iconst(self.pointer, 0),
            [var] => {
                let word = self.b.use_var(*var);
                let zero = self.iconst(0);
                self.b.def_var(*var, zero);
                word
            }
            _ => unreachable!("one function value to drop at most"),
        };
        let drop_env = match env {
            Some(var) => {
                let word = self.b.use_var(var);
                let zero = self.iconst(0);
                self.b.def_var(var, zero);
                word
            }
            None => self.iconst(0),
        };
        let not_tail = self.iconst(0);
        let mut call_args = vec![self.ctx, self.frames, drops, drop_env, not_tail];
        call_args.extend(fv);
        call_args.extend(args.iter().flatten());
        let r = self.call(self.apply_any[&n], &call_args);
        let r: Vec<ir::BlockArg> = r.into_iter().map(Into::into).collect();
        self.b.ins().jump(returned, &r);

        // Out of steps or frames before the call: what is held (the
        // machine's `push` drops the `Ret` first), then the arguments and
        // the function value, then the rest.
        self.b.switch_to_block(unready);
        self.b.set_cold_block(unready);
        self.release(held);
        for v in args {
            self.drop_value(*v);
        }
        self.drop_value(fv);
        for var in pre {
            self.drop_fun_var(*var);
        }
        if let Some(var) = env {
            self.drop_fun_var(var);
        }
        self.leave();

        // The value, or the callee's error or tail request.
        self.b.switch_to_block(returned);
        let r = self.b.block_params(returned).to_vec();
        let error = self
            .b
            .ins()
            .load(types::I64, flags(), self.ctx, Context::ERROR_AT);
        let ok = self.b.create_block();
        for _ in 0..3 {
            self.b.append_block_param(ok, types::I64);
        }
        let check = self.b.create_block();
        let r_args: Vec<ir::BlockArg> = r.iter().map(|x| (*x).into()).collect();
        self.b.ins().brif(error, check, &[], ok, &r_args);
        self.b.switch_to_block(check);
        self.b.set_cold_block(check);
        let requested = self
            .b
            .ins()
            .icmp_imm_u(IntCC::Equal, error, TAIL_REQUEST as i64);
        let perform = self.b.create_block();
        let failed = self.b.create_block();
        self.b.ins().brif(requested, perform, &[], failed, &[]);
        self.b.switch_to_block(perform);
        self.b.set_cold_block(perform);
        let out = self.addr(self.scratch, 0);
        steps_out(self.b, self.ctx);
        self.call(self.helpers.perform, &[self.ctx, self.frames, out]);
        steps_in(self.b, self.ctx);
        let v = self.load(self.scratch, 0);
        let error = self
            .b
            .ins()
            .load(types::I64, flags(), self.ctx, Context::ERROR_AT);
        let v_args: Vec<ir::BlockArg> = v.iter().map(|x| (*x).into()).collect();
        self.b.ins().brif(error, failed, &[], ok, &v_args);
        self.b.switch_to_block(failed);
        self.b.set_cold_block(failed);
        self.release(held);
        self.leave();

        self.b.switch_to_block(ok);
        let p = self.b.block_params(ok);
        [p[0], p[1], p[2]]
    }

    /// `fv args` (all moved in) in a tail position: ends the block. The
    /// leaving frame's closure `env` goes as for [`Rt::apply`].
    fn tail_apply(&mut self, fv: Words, args: &[Words], env: Variable) {
        let n = args.len() as u32;
        let target = self.target_of(fv, n);
        let exact = self.b.create_block();
        let slow = self.b.create_block();
        self.b.ins().brif(target, exact, &[], slow, &[]);

        self.b.switch_to_block(exact);
        let unready = self.b.create_block();
        self.count_step(unready);
        self.check_frame(unready);
        self.drop_fun_var(env);
        let pushed = self.b.ins().iadd_imm_s(self.frames, 1);
        let mut call_args = vec![self.ctx, pushed];
        call_args.extend(args.iter().flatten());
        call_args.push(fv[1]);
        let signature = self.b.import_signature(value_signature(self.pointer, n));
        self.b
            .ins()
            .return_call_indirect(signature, target, &call_args);

        self.b.switch_to_block(unready);
        self.b.set_cold_block(unready);
        for v in args {
            self.drop_value(*v);
        }
        self.drop_value(fv);
        self.drop_fun_var(env);
        self.leave();

        // Through the stub, as a tail apply: it drops the closure once it
        // has taken `fv` apart, or leaves it with a tail request.
        self.b.switch_to_block(slow);
        let drop_env = self.b.use_var(env);
        let tail = self.iconst(1);
        let none = self.b.ins().iconst(self.pointer, 0);
        let mut call_args = vec![self.ctx, self.frames, none, drop_env, tail];
        call_args.extend(fv);
        call_args.extend(args.iter().flatten());
        let apply = self.fref(self.apply_any[&n]);
        self.b.ins().return_call(apply, &call_args);
    }
}

/// What the runtime bodies are emitted with.
pub(crate) struct Emit<'b> {
    pub(crate) helpers: &'b Helpers,
    pub(crate) apply_any: &'b BTreeMap<u32, FuncId>,
    pub(crate) runtime: Runtime,
    pub(crate) pointer: ir::Type,
    pub(crate) options: Options,
    /// `Call`'s tag (`Shapes::call`), for a `translate`'s operation.
    pub(crate) call_tag: u32,
}

fn begin<'a, 'b>(
    b: &'b mut FunctionBuilder<'a>,
    module: &'b mut dyn Module,
    caches: &'b mut u32,
    emit: &Emit<'b>,
) -> (Rt<'a, 'b>, Vec<IrValue>) {
    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let params = b.block_params(entry).to_vec();
    let scratch = b.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        VALUE_SIZE as u32,
        3,
    ));
    let rt = Rt {
        b,
        module,
        helpers: emit.helpers,
        apply_any: emit.apply_any,
        caches,
        pointer: emit.pointer,
        options: emit.options,
        refs: BTreeMap::new(),
        ctx: params[0],
        frames: params[1],
        scratch,
    };
    (rt, params)
}

/// `rt_loop` (`loop_signature`; the module comment).
pub(crate) fn emit_loop(
    b: &mut FunctionBuilder<'_>,
    module: &mut dyn Module,
    caches: &mut u32,
    emit: &Emit<'_>,
) {
    let (mut rt, params) = begin(b, module, caches, emit);
    let c_slot = rt.slot(1);
    let pending_slot = rt.slot(1);
    let out_slot = rt.slot(3);
    let k_slot = rt.slot(1);
    let cell_slot = rt.slot(2);
    let handler = rt.b.declare_var(types::I64);
    let env = rt.b.declare_var(rt.pointer);
    rt.store(c_slot, 0, [params[2], params[3], params[4]]);
    rt.store(pending_slot, 0, [params[5], params[6], params[7]]);
    rt.b.def_var(handler, params[8]);
    rt.b.def_var(env, params[9]);
    let top = rt.b.create_block();
    rt.b.ins().jump(top, &[]);

    // A step, then what the computation is.
    rt.b.switch_to_block(top);
    let out_of_steps = rt.b.create_block();
    rt.count_step(out_of_steps);
    let c_at = rt.addr(c_slot, 0);
    let pending_at = rt.addr(pending_slot, 0);
    let out_at = rt.addr(out_slot, 0);
    let word = rt.b.use_var(handler);
    let action = rt.call(
        rt.helpers.eff_step,
        &[rt.ctx, c_at, pending_at, word, out_at],
    )[0];
    let applying = rt.b.create_block();
    let returning = rt.b.create_block();
    let done = rt.b.create_block();
    let calling = rt.b.create_block();
    let injecting = rt.b.create_block();
    let trap = rt.b.create_block();
    let mut switch = Switch::new();
    switch.set_entry(u128::from(abi::STEP_AGAIN), top);
    switch.set_entry(u128::from(abi::STEP_APPLY), applying);
    switch.set_entry(u128::from(abi::STEP_RETURN), returning);
    switch.set_entry(u128::from(abi::STEP_DONE), done);
    switch.set_entry(u128::from(abi::STEP_CALL), calling);
    switch.set_entry(u128::from(abi::STEP_INJECT), injecting);
    switch.emit(rt.b, action, trap);
    rt.b.switch_to_block(trap);
    rt.b.set_cold_block(trap);
    rt.b.ins().trap(TrapCode::unwrap_user(4));

    // `Done x` with `k` pending: `k x`, its result the next computation.
    rt.b.switch_to_block(applying);
    let k = rt.load(out_slot, 0);
    let x = rt.load(out_slot, 1);
    let held = [Hold::Handler(handler), Hold::Value(pending_slot)];
    let v = rt.apply(k, &[x], &[], Some(env), &held);
    rt.store(c_slot, 0, v);
    rt.b.ins().jump(top, &[]);

    // The loop's value.
    rt.b.switch_to_block(returning);
    let v = rt.load(out_slot, 0);
    rt.drop_fun_var(env);
    rt.b.ins().return_(&v);

    // A fold's `done x`.
    rt.b.switch_to_block(done);
    let f = rt.load(out_slot, 0);
    let x = rt.load(out_slot, 1);
    rt.tail_apply(f, &[x], env);

    // A fold's `call o k`.
    rt.b.switch_to_block(calling);
    let f = rt.load(out_slot, 0);
    let o = rt.load(out_slot, 1);
    let k = rt.load(out_slot, 2);
    rt.tail_apply(f, &[o, k], env);

    // A `translate`'s operation: `Call (inject o) k`.
    rt.b.switch_to_block(injecting);
    let inject = rt.load(out_slot, 0);
    let o = rt.load(out_slot, 1);
    let k = rt.load(out_slot, 2);
    rt.store(k_slot, 0, k);
    let v = rt.apply(inject, &[o], &[], Some(env), &[Hold::Value(k_slot)]);
    let k = rt.load(k_slot, 0);
    rt.store(cell_slot, 0, v);
    rt.store(cell_slot, 1, k);
    let fields = rt.addr(cell_slot, 0);
    let out = rt.addr(out_slot, 0);
    let tag = rt.b.ins().iconst(types::I32, i64::from(emit.call_tag));
    let two = rt.iconst(2);
    rt.call(rt.helpers.ctor, &[tag, fields, two, out]);
    let cell = rt.load(out_slot, 0);
    rt.b.ins().return_(&cell);

    // Out of steps: everything given up, dropped at once (no frame has
    // left), as the machine's `eff_run` drops what it holds.
    rt.b.switch_to_block(out_of_steps);
    rt.b.set_cold_block(out_of_steps);
    rt.release(&[
        Hold::Value(c_slot),
        Hold::Handler(handler),
        Hold::Value(pending_slot),
        Hold::Fun(env),
    ]);
    rt.leave();
}

/// `rt_resume` (`resume_signature`; the module comment).
pub(crate) fn emit_resume(
    b: &mut FunctionBuilder<'_>,
    module: &mut dyn Module,
    caches: &mut u32,
    emit: &Emit<'_>,
) {
    let (mut rt, params) = begin(b, module, caches, emit);
    let y_slot = rt.slot(1);
    let out_slot = rt.slot(5);
    let pending_slot = rt.slot(1);
    let rest_slot = rt.slot(1);
    let handler_slot =
        rt.b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 3));
    let handler = rt.b.declare_var(types::I64);
    let k = rt.b.declare_var(types::I64);
    let env = rt.b.declare_var(rt.pointer);
    rt.store(y_slot, 0, [params[2], params[3], params[4]]);
    rt.b.def_var(k, params[5]);
    rt.b.def_var(env, params[6]);
    let y_at = rt.addr(y_slot, 0);
    let out_at = rt.addr(out_slot, 0);
    let handler_at = rt.b.ins().stack_addr(rt.pointer, handler_slot, 0);
    let word = rt.b.use_var(k);
    let translating = rt.call(rt.helpers.resume_begin, &[word, y_at, out_at, handler_at])[0];
    let word = rt.b.ins().load(types::I64, flags(), handler_at, 0);
    rt.b.def_var(handler, word);
    let pending = rt.load(out_slot, 0);
    rt.store(pending_slot, 0, pending);
    let rest = rt.load(out_slot, 1);
    rt.store(rest_slot, 0, rest);
    let finish = rt.b.create_block();
    for _ in 0..3 {
        rt.b.append_block_param(finish, types::I64);
    }
    let translate = rt.b.create_block();
    let plain = rt.b.create_block();
    rt.b.ins().brif(translating, translate, &[], plain, &[]);

    // `rest y`.
    rt.b.switch_to_block(plain);
    let rest = rt.load(rest_slot, 0);
    let y = rt.load(out_slot, 2);
    let held = [Hold::Handler(handler), Hold::Value(pending_slot)];
    let v = rt.apply(rest, &[y], &[k], Some(env), &held);
    let v_args: Vec<ir::BlockArg> = v.iter().map(|x| (*x).into()).collect();
    rt.b.ins().jump(finish, &v_args);

    // A `translate`'s: `rest (reply o y)`.
    rt.b.switch_to_block(translate);
    let reply = rt.load(out_slot, 2);
    let o = rt.load(out_slot, 3);
    let y = rt.load(out_slot, 4);
    let held = [
        Hold::Value(rest_slot),
        Hold::Handler(handler),
        Hold::Value(pending_slot),
    ];
    let replied = rt.apply(reply, &[o, y], &[k], Some(env), &held);
    let rest = rt.load(rest_slot, 0);
    let held = [Hold::Handler(handler), Hold::Value(pending_slot)];
    let v = rt.apply(rest, &[replied], &[], None, &held);
    let v_args: Vec<ir::BlockArg> = v.iter().map(|x| (*x).into()).collect();
    rt.b.ins().jump(finish, &v_args);

    // The loop from the result, with what was pending at the operation.
    rt.b.switch_to_block(finish);
    let v = rt.b.block_params(finish).to_vec();
    let pending = rt.load(pending_slot, 0);
    let word = rt.b.use_var(handler);
    let none = rt.b.ins().iconst(rt.pointer, 0);
    let run_loop = rt.fref(emit.runtime.run_loop);
    let mut call_args = vec![rt.ctx, rt.frames];
    call_args.extend(v);
    call_args.extend(pending);
    call_args.push(word);
    call_args.push(none);
    rt.b.ins().return_call(run_loop, &call_args);
}
