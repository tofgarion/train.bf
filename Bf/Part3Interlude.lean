import Bf.Part3



namespace Zen.Train.Bf

/-! # Stackless?

Despite `Rt.Spec.runWithStack` seeming tailrec, the fact that it produces `Mon Unit` means that
dependending on what `Mon` actually is, it might not be tailrec.

Lean has very good support for monads as they're used everywhere, but in this case it's not able to
specialize `Rt.Spec.runWithStack` enough so that the code generated is itself tailrec.

- demo with `Main.lean`



Below is exactly the same function, but this time `IO` is not a type parameter.

- demo with `Main.lean` again
-/



@[always_inline, inline]
partial def Rt.IO.runWithStack (stack : Rt.Stack) : Ast → Rt.BfT IO Unit
| .op o => do
  Rt.IO.op o
  goUp stack
| .seff s => do
  Rt.IO.seff s
  goUp stack
| .check c => do
  Rt.IO.check c
  goUp stack
| .block b => do
  if ← Rt.IO.isZeroCurr then goUp stack else
    let val ← Rt.IO.getCurr
    Rt.IO.runWithStack (.block val 0 b :: stack) b
| .seq s =>
  if h : 0 < s.size then
    let stack := .seq s ⟨0, h⟩ :: stack
    Rt.IO.runWithStack stack s[0]
  else goUp stack
where
  @[always_inline, inline]
  goUp : Rt.Stack → Rt.BfT IO Unit
  | [] => return ()
  | .seq s idx :: stack =>
    let idx := idx.val + 1
    if h : idx < s.size then
      let stack := .seq s ⟨idx, h⟩ :: stack
      Rt.IO.runWithStack stack s[idx]
    else
      goUp stack
  | .block oldVal count body :: stack => do
    if ← Rt.IO.isZeroCurr then goUp stack else
      let val ← Rt.IO.getCurr
      let count := if val < oldVal then count else count.succ
      let loopLimit ← Rt.IO.getLoopLimit
      if let some limit := loopLimit then
        if h_lt : limit < count then
          Rt.Error.loopLimit limit count h_lt
          |> Rt.IO.throw
      Rt.IO.runWithStack (.block val count body :: stack) body

def Ast.fastEvalIOTo!
  [Inhabited α]
  (code : Ast) (inputs : List Nat) (ex : Rt.Extract α) (config := Rt.Config.default)
: IO α := do
  let state := Rt.State.mk inputs (config := config)
  match ← (Rt.IO.runWithStack [] code : Rt.BfT IO Unit) state with
  | .ok _ state =>
    match ex.apply state.outputs with
    | .ok res => return res
    | .error e => IO.throwServerError s!"{e}"
  | .error err _ => IO.throwServerError s!"{err}"
