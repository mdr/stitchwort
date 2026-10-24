-- The Stitchwort prelude (the core), loaded before every file. It is the files
-- of `std/core/`, checked as one module in the order `CORE_FILES` lists them
-- (crates/elab/src/lib.rs): this file first, so the import below covers all of
-- them, and each file only uses what the files before it declare. Why each
-- file is in the core: docs/proposals/prelude-slim.md §2.1.
-- core/Imports.sw holds this header and the effect imports.

-- The library's root is `Std` (docs/proposals/namespaces.md). What's declared
-- here without a namespace is visible in every program; the rest is written
-- with its namespace (`List.length`), or imported. The effect machinery is
-- used throughout what follows, so it's imported here.
import Effect (
  Comp,
  foldComp,
  bind,
  Plus,
  PlusRes,
  SigMap,
  sigInject,
  sigReply,
  translate,
  sigId,
  sigCompose,
  sigLeft,
  sigRight,
  swapOp,
  swapReply,
  sigSwap,
  NoOp,
  NoRes,
  caseInject,
  caseReply,
  sigCase,
  noInject,
  noReply,
  sigFromNo,
  handlePlus,
  runPure,
  Effects,
  rowOp,
  rowRes,
  CompIn,
  doneIn,
  bindIn,
  liftIn,
  lowerIn,
  Rec,
  RecRes,
  Delay,
  now,
  lift,
  bindD,
  mapSig,
  pfix
)
