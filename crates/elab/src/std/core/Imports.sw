--| The Stitchwort prelude (the core), loaded before every file.
--| core/Imports.sw holds this header and the effect imports.
-- It is the files of `std/core/`, checked as one module in the order
-- `core/order.txt` lists them: this file first, so the
-- import below covers all of them, and each file only uses what the files
-- before it declare. Why each file is in the core:
-- docs/proposals/prelude-slim.md §2.1.

--| The library's root is `Std`. What's declared here without a namespace is
--| visible in every program; the rest is written with its namespace
--| ([`List.length`]), or imported.
-- (docs/proposals/namespaces.md)
-- The effect machinery is used throughout what follows, so it's imported
-- here.
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
  pfix,
  Divergence,
  CompD,
  doneD,
  bindDv,
  liftD,
  delayD
)
