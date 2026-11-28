use super::*;

pub fn generate(g: &View<'_>, limits: Limits) -> Result<Output, Diagnostic> {
    generate_with(g, limits, Options::default())
}

/// [`generate`], with the given representation options.
pub fn generate_with(g: &View<'_>, limits: Limits, options: Options) -> Result<Output, Diagnostic> {
    let ids: Vec<DefId> = (0..g.env.defs().len())
        .map(DefId)
        .filter(|id| g.def(*id).export())
        .collect();
    generate_exports(g, limits, options, &ids)
}

/// [`generate_with`] for the exports `ids` only: one namespace's.
pub fn generate_exports(
    g: &View<'_>,
    limits: Limits,
    options: Options,
    ids: &[DefId],
) -> Result<Output, Diagnostic> {
    let _op = g.machine.budget.operation(Limits::stack_only(limits.stack));
    let exports = ids
        .iter()
        .map(|id| exportable(g, *id))
        .collect::<Result<Vec<_>, _>>()?;

    let boundary_datas = check_names(g, &exports)?;
    let inputs = input_datas(g, &boundary_datas)?;
    // Read once here, where a resource refusal can still be reported: the
    // generator below reads them repeatedly, from places that only build
    // strings (SW-3960).
    let fields: HashMap<DataId, Vec<Vec<(String, Boundary)>>> = boundary_datas
        .iter()
        .map(|&d| export_field_boundaries(g, d).map(|fields| (d, fields)))
        .collect::<Result<_, _>>()?;

    // A map that crosses is built and read with the library's own `Map`
    // functions, so they're generated, with the `Text` order they're given.
    let maps_cross = exports
        .iter()
        .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
        .any(Boundary::has_map)
        || fields
            .values()
            .any(|fields| fields.iter().flatten().any(|(_, b)| b.has_map()));
    let map_defs: Vec<DefId> = if maps_cross {
        [
            Builtin::MapFromList,
            Builtin::MapToList,
            Builtin::TextInstOrd,
        ]
        .into_iter()
        .map(|b| {
            g.env
                .registry()
                .loaded_def(b)
                .expect("a map crosses only with the library's `Map` loaded")
        })
        .collect()
    } else {
        Vec::new()
    };
    erasable(g)?;
    let codegen = Gen::new(g, options, fields)?;
    // Only what the exports use, in declaration order. That's dependency
    // order: the kernel admits each group only once what it uses is final,
    // so a definition refers only to earlier ones and to members of its own
    // group. Those are thunks or functions, never values, so they look each
    // other up only when called, after all of them are defined.
    // What records' proof-field checks use, too.
    // And the helpers of their fields' defaults, which decoders call for
    // missing properties (docs/proposals/named-arguments.md §5.3).
    let checks = boundary_datas
        .iter()
        .flat_map(|d| g.data(*d).validators())
        .flat_map(|v| v.decision.subterms())
        .filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        })
        .chain(boundary_datas.iter().flat_map(|d| {
            g.defaults(*d)
                .into_iter()
                .flat_map(|table| table.iter().flatten().flatten())
                .map(|default| default.helper)
        }));
    let checks = checks.chain(map_defs.iter().copied());
    let wanted = codegen.set_reach(exports.iter().map(|sig| sig.id).chain(checks), &[], true)?;
    let mut js = String::from(RUNTIME);
    js.push('\n');
    if codegen.float.is_some() {
        js.push_str(FLOAT_BITS);
    }
    if codegen.array.is_some() {
        js.push_str(VERSION_ARRAYS);
    }
    if codegen.text.is_some() {
        js.push_str(TEXT_AS_STRING);
        js.push_str(CHARS_OF_TEXT);
        js.push_str(TEXT_OF_CHARS);
    } else {
        js.push_str(TEXT_AS_LIST);
        js.push_str(CHARS_OF_TEXT);
    }
    // `INT` only where it's used.
    let crosses = |leaf: Boundary| {
        let at_boundary = |b: &Boundary| b.mentions(&leaf);
        exports
            .iter()
            .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
            .any(at_boundary)
            || codegen
                .fields
                .values()
                .any(|fields| fields.iter().flatten().any(|(_, b)| at_boundary(b)))
    };
    let safe_nat_crosses = crosses(Boundary::SafeNat);
    let safe_int_crosses = crosses(Boundary::SafeInt);
    if let Some(int) = int_data(g).filter(|_| safe_int_crosses || crosses(Boundary::Int)) {
        js.push_str(&codegen.int_codec(int));
    }
    if crosses(Boundary::Float) {
        js.push_str(FLOAT_CODEC);
    }
    if safe_nat_crosses || safe_int_crosses {
        js.push_str(&codegen.safe_codecs(
            safe_nat_data(g).filter(|_| safe_nat_crosses),
            safe_int_data(g).filter(|_| safe_int_crosses),
        ));
    }
    js.push_str(RUNTIME_CODECS);
    js.push_str(RUNTIME_FAST);
    js.push('\n');
    // Every data type is declared before any is defined, so their fields'
    // types can refer to each other (and themselves).
    for &d in &boundary_datas {
        let data = g.data(d);
        let tag_key = repr(g, d).tag_key.clone();
        // The tag key, unless it's the default (or the type is a record).
        let key = if data.record() || tag_key == js_repr::DEFAULT_TAG_KEY {
            String::new()
        } else {
            format!(", {}", js_string_literal(&tag_key))
        };
        let _ = writeln!(
            js,
            "const {} = datatype({}{key});",
            info_name(data.path()),
            js_string_literal(data.name())
        );
    }
    // How the runtime builds and takes apart an `Option`.
    if let Some(&d) = boundary_datas
        .iter()
        .find(|d| g.env.registry().is_data(Builtin::Option, **d))
    {
        let data = g.data(d);
        let some = &data.ctors()[1];
        let _ = writeln!(
            js,
            "const OPTION_SHAPE = {{ info: {}, none: {}, some: {}, key: {} }};",
            info_name(data.path()),
            js_string_literal(&data.ctors()[0].name),
            js_string_literal(&some.name),
            js_string_literal(&field_key_at(g, d, 1, 0)),
        );
    }
    for &d in &boundary_datas {
        js.push_str(&codegen.define(d)?);
    }
    js.push('\n');
    // Partial computations are one token (docs/proposals/partial.md §7.6).
    let mut any_delay = false;
    for &id in &wanted {
        any_delay |= codegen.info(id)?.delay.is_some();
    }
    if any_delay {
        js.push_str("// A partial computation, which nothing here can run.\nconst delayed = Symbol(\"Delay\");\n\n");
    }
    if let Some(effect) = &codegen.effect
        && wanted.iter().any(|id| effect.native(*id).is_some())
    {
        js.push_str(effect.runtime());
        js.push('\n');
    }
    let while_generating = |id: DefId| {
        move |e: Diagnostic| e.with_label(g.def(id).span(), "while generating JavaScript for this")
    };
    let mut runnable = Vec::with_capacity(wanted.len());
    for id in wanted {
        if codegen.info(id)?.delay.is_none() {
            runnable.push(id);
        }
    }
    let wanted = runnable;
    let mut mapper = sourcemap::Mapper::new(&js);
    for id in dependency_order(&codegen, &wanted) {
        // Only an admitted definition has a body. The driver doesn't extract
        // a module with errors, but if it were asked to, the JS would call a
        // function that isn't there.
        let def = g.def(id);
        if def.body().is_none() && !codegen.info(id)?.result_erased && !codegen.is_native(id) {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!("can't generate JavaScript for `{}`", def.name()),
            )
            .with_label(
                def.span(),
                "it hasn't been checked successfully, so it has no definition to generate",
            ));
        }
        let text = codegen.def(id).map_err(while_generating(id))?;
        mapper.chunk(&js, &text, def.span(), def.name());
        js.push_str(&text);
    }
    mapper.end(&js);
    if maps_cross {
        js.push_str(&codegen.map_shape()?);
    }
    for sig in &exports {
        let text = codegen.wrapper(sig).map_err(while_generating(sig.id))?;
        mapper.chunk(&js, &text, g.def(sig.id).span(), &sig.name);
        js.push_str(&text);
    }
    mapper.end(&js);
    js.push_str(&codegen.fast.borrow().module_text());
    js.push_str(&codegen.hoisted_vars());
    // Exports aren't names in the module's scope, so they can't hide its
    // own names or the JS globals it uses (`Set`, `BigInt`, …).
    let exported: Vec<String> = exports
        .iter()
        .map(|sig| format!("{} as {}", wrapper_name(&sig.name), sig.name))
        .collect();
    if !exported.is_empty() {
        let _ = writeln!(js, "\nexport {{ {} }};", exported.join(", "));
    }

    let mut dts = String::from(
        "// Generated by stitchwort. Do not edit.\n\nexport declare class StitchwortInputError extends Error {}\nexport declare class StitchwortResourceError extends Error {}\n",
    );
    // `Option` has a declaration only where a nested one is the tagged union.
    let tagged_option = exports
        .iter()
        .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
        .any(|b| names_option(g, b))
        || codegen
            .fields
            .values()
            .any(|fields| fields.iter().flatten().any(|(_, b)| names_option(g, b)));
    for &d in &boundary_datas {
        if g.env.registry().is_data(Builtin::Option, d) && !tagged_option {
            continue;
        }
        dts.push_str(&codegen.ts_alias(d, None));
        // Its input shape, next to it, if it has one.
        if inputs.contains(&d) {
            dts.push_str(&codegen.ts_alias(d, Some(&inputs)));
        }
    }
    for sig in &exports {
        let params: Vec<String> = sig
            .params
            .iter()
            .map(|(x, b)| format!("{x}: {}", codegen.ts_type(b, true, &[], Some(&inputs))))
            .collect();
        let _ = writeln!(
            dts,
            "export declare function {}({}): {};",
            sig.name,
            params.join(", "),
            codegen.ts_type(&sig.result, false, &[], None)
        );
    }
    Ok(Output {
        js,
        dts,
        mappings: mapper.finish(),
    })
}
/// Erasing `Delay` values to one token is correct only while no code can tell
/// two of them apart (docs/proposals/partial.md §7.6): `Delay` has no
/// eliminator and its constants no computation rules. A definition is how
/// the kernel would give one a rule, so a `Delay` constant with a body means
/// erasure must be replaced by a real representation.
pub(crate) fn erasable(g: &View<'_>) -> Result<(), Diagnostic> {
    for prim in Primitive::ALL {
        // Each of these builds a `Delay` (or is the type): none observes one.
        let builds = match prim {
            Primitive::Delay
            | Primitive::Now
            | Primitive::Lift
            | Primitive::BindD
            | Primitive::MapSig
            | Primitive::Pfix
            | Primitive::FoldD => true,
        };
        if let Some(id) = g.env.builtins().primitive_id(prim)
            && (!builds || g.def(id).body().is_some())
        {
            return Err(Diagnostic::error(
                "E-JS-PARTIAL",
                "partial computations can't be extracted to JavaScript",
            )
            .with_label(
                g.def(id).span(),
                format!(
                    "`{}` computes, so `Delay` values can't all be erased to one token",
                    prim.name()
                ),
            ));
        }
    }
    Ok(())
}
