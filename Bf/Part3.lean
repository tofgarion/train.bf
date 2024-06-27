import Bf.Part2



/-! # Abstract runtime: non-trivial code and monads -/
namespace Zen.Train.Bf



/-! Whatever the effect of the `Op`-s, `Seff`-s and `Check`-s, the nodes of the AST (`Ast.block` and
`Ast.seq`) have the same semantics as long as we can check the value of the current cell.

Let's write an abstract interpreter that handles the nodes and defers to semantics to define later
-/


namespace Rt


/-- Frames of the abstract interpreter.

The interpreter is going to be tailrec, obviously, so we have to handle the `Stack` (list of
`Frame`s) by hand. The frames store the information needed to deal with the nodes of the AST
(`Ast.seq` and `Ast.block`). When we interpret an `Ast.seq` for instance, we need to *go down*
(execute) the first element, and once that's over we *go up* (look in the stack) to find the frame
with the information needed to run the second element (if any), and so on.
-/
inductive Frame
/--
Stores the elements of the sequence, and a pointer telling us which elements we are currently in. So
when we go up the stack and see `Frame.seq elems i` we know we just executed the `elems[i]`; we now
need to check whether we're done with the sequence, and if not update the frame to point to the next
element and go down that element.
-/
| seq : (array : Array Ast) → Fin array.size → Frame
/--
Stores the `oldVal` and `count` quantities discussed in the documentation of module `Bf.Part2`, and
the body of the block.
-/
| block (oldVal : Nat) (count : Nat) : Ast → Frame



/-- A list of `Frame`s. -/
abbrev Stack := List Frame



/-- Abstracts over the runtime memory and the semantics of the operations. -/
class Spec (Mon : Type → Type u) where
  /-- Applies an operator. -/
  op : Ast.Op → Mon Unit
  /-- Applies a side-effect. -/
  seff : Ast.Seff → Mon Unit
  /-- Runs a check. -/
  check : Ast.Check → Mon Unit
  /-- Yields the current cell value. -/
  getCurr : Mon Nat
  /-- The loop limit, see `Frame`'s documentation for details. Note that it does not need to be
  static. -/
  getLoopLimit : Mon $ Option Nat
  /-- Throws an error. -/
  throw : Error → Mon α

namespace Spec

variable {Mon : Type → Type u} [Monad Mon]

def isZeroCurr [Self : Spec Mon] : Mon Bool :=
  --      vvv~~~~~ `Functor.map`, comes for free as `Monad Mon` implies `Functor Mon`
  (· = 0) <$> Self.getCurr

#checkout Functor



namespace run.Test
/-! Time to do something!

Write a `scoped instance TestRt : Spec (StateT State IO)`.

We will use it for testing in a few moments, I **strongly** suggest you take a look at my version
once you're done to avoid having problems in both `TestRt` and what we're about to test with it.

Alternatively, consider calling your version `TestRt'` and using my version once you're done writing
yours.
-/

#checkout StateT

scoped instance TestRt : Spec (StateT State IO) where
  op op := do
    let state ← get
    set (state.applyOp op)
  seff
  | .out => fun s => return ((), s.emit s.getCurr)
  | .inp => fun s =>
    let (val, s) := s.drainInput
    return ((), s.mapCurr (𝕂 val))
  | .dbg msg => println! msg
  check
  | .chk exp msg, s => do
    let val := s.getCurr
    if val ≠ exp
    then IO.throwServerError s!"check failed: {val} ≠ {exp}, {msg}"
    else return ((), s)
  getCurr := do
    return (← get).getCurr
  getLoopLimit := return some 1
  throw e := do
    IO.throwServerError s!"{e}"
end run.Test


/-! Write `def runWithStack [Self : Spec Mon] : Stack → Ast → Mon Unit`.

(I omitted `Mon` and its `Monad` instance in this signature as they are variables.)

(Strong) suggestion: use `where` to define a helper `goUp : Stack → Mon Unit`.

```
def runWithStack ...
  ...
where
  goUp : Stack → Mon Unit
    ...
```
-/

section sol!
partial def runWithStack [Self : Spec Mon] (stack : Stack) : Ast → Mon Unit
| .op o => do
  Self.op o
  goUp stack
| .seff s => do
  Self.seff s
  goUp stack
| .check c => do
  Self.check c
  goUp stack
| .block b => do
  if ← Self.isZeroCurr then goUp stack else
    let val ← Self.getCurr
    Self.runWithStack (.block val 0 b :: stack) b
| .seq s =>
  if h : 0 < s.size then
    let stack := .seq s ⟨0, h⟩ :: stack
    Self.runWithStack stack s[0]
  else goUp stack
where
  goUp : Stack → Mon Unit
  | [] => return ()
  | .seq s idx :: stack =>
    let idx := idx.val + 1
    if h : idx < s.size then
      let stack := .seq s ⟨idx, h⟩ :: stack
      Self.runWithStack stack s[idx]
    else
      goUp stack
  | .block oldVal count body :: stack => do
    if ← Self.isZeroCurr then goUp stack else
      let val ← Self.getCurr
      let count := if val < oldVal then count else count.succ
      let loopLimit ← Self.getLoopLimit
      if let some limit := loopLimit then
        if h_lt : limit < count then
          Error.loopLimit limit count h_lt
          |> Self.throw
      Self.runWithStack (.block val count body :: stack) body
end sol!

/-- info:
Zen.Train.Bf.Rt.Spec.runWithStack.{u} {Mon : Type → Type u} [Monad Mon] [Self : Spec Mon] (stack : Stack) :
  Ast → Mon Unit
-/
#guard_msgs in #check runWithStack



abbrev justRun [Self : Spec Mon] : Ast → Mon Unit :=
  Self.runWithStack []



namespace run.Test
def run (ast : Ast) (inputs : List Nat := []) : IO (Array Nat) := do
  let state := State.mk inputs
  let (_, state) ← TestRt.justRun ast state
  return state.outputs

/-- error:
potential infinite loop detected after 2 non-decreasing iterations (limit is 1)
-/
#guard_msgs(error, drop info) in #eval do
  -- `+[]` (infinite loop)
  let ast := Ast.seq #[.inc, .blockSeq #[]]
  run ast

/--
info: done, let's fail now
---
error: check failed: 0 ≠ 3, expected failure 🐙
-/
#guard_msgs in #eval do
  -- `>+++<` (move right, add 3, move left)
  let ast := Ast.seq #[
    .chk 0 "should be 0",
    .mvr,
    .chk 0 "should be 0 too",
    .inc, .inc, .inc,
    .chk 3 "should be 3",
    .mvl,
    .chk 0 "should still be 0",
    .dbg "done, let's fail now",
    .chk 3 "expected failure 🐙"
  ]
  run ast

/-- info:
copying left
not done
not done
not done
done
#[0, 3]
-/
#guard_msgs in #eval do
  -- `,[->+<].>.` (read input and copy it to the next cell)
  let ast := Ast.seq #[
    .inp,
    .dbg "copying left",
    .blockSeq #[.dbg "not done", .dec, .mvr, .inc, .mvl],
    .dbg "done",
    .out, .mvr, .out
  ]
  --       v~~ loop limit is `1`, but the loop checks decreasing values
  run ast [3]

end run.Test

end Spec



/-! Great so at this point we have

- a notion of `State` (with internal `Mem`ory), and
- a `Spec`ification with an abstract `Spec.run` function

we need to have a clean way to deal with errors and monad-related stuff.

We're going to define a `BfT` error/state monad transformer 🙀. Remember

- state monad transformer: `abbrev StateM σ M α := σ → M (α × σ)`, no way to report errors without
  making some assumption on `M`;
- error monad: `inductive Except ε α | ok α | error ε`.

(Try to) define `BfT M α`, the error/state monad with fixed state `State`.

Note that, as is often the case we want to be able to access the state even when an error is
produced. It's useful for debugging.
-/

section sol!
/-!
It **might** be a good idea to introduce a first definition, potentially called `BfT.Res`.
-/

inductive BfT.Res (α : Type)
| ok : α → State → Res α
| error : Error → State → Res α

abbrev BfT (M : Type → Type) (α : Type) :=
  State → M (BfT.Res α)
end sol!



/-! Great, make sure you have my version now. -/

namespace BfT.Res
/-! Is `BfT.Res` a (reasonable) monad?

Is there a `bind`-like operation that would make sense here?
-/

section sol!
instance instFunctor : Functor Res where
  map
  | f, ok val s => ok (f val) s
  | _, error e s => error e s

def map (f : α → β) (self : Res α) :=
  f <$> self
end sol!
end BfT.Res



namespace BfT
variable {M : Type → Type} [Monad M]


/-! Let's write a bunch of functions 🐙 -/

section sol!
def throw : Error → BfT M α :=
  (.error · · |> pure)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.throw {M : Type → Type} [Monad M] {α : Type} : Error → BfT M α
-/
#guard_msgs in #check throw

section sol!
def throwLoopLimit : (limit : Nat) → (count : Nat) → limit < count → BfT M α :=
  (.loopLimit · · · |> throw)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.throwLoopLimit {M : Type → Type} [Monad M] {α : Type} (limit count : Nat) : limit < count → BfT M α
-/
#guard_msgs in #check throwLoopLimit

section sol!
def throwCheckFailed (msg : String) (exp val : Nat) (h_ne : exp ≠ val) : BfT M α :=
  throw <| .checkFailed msg exp val h_ne
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.throwCheckFailed {M : Type → Type} [Monad M] {α : Type} (msg : String) (exp val : Nat)
  (h_ne : exp ≠ val) : BfT M α
-/
#guard_msgs in #check throwCheckFailed

section sol!
def getState : BfT M State
| state => return .ok state state
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.getState {M : Type → Type} [Monad M] : BfT M State
-/
#guard_msgs in #check getState

section sol!
def setState : State → BfT M Unit
| state, _ => return .ok () state
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.setState {M : Type → Type} [Monad M] : State → BfT M Unit
-/
#guard_msgs in #check setState

section sol!
def mapMStateAnd : (State → M (α × State)) → BfT M α
| f, state => do
  let (res, state) ← f state
  return .ok res state
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.mapMStateAnd {M : Type → Type} [Monad M] {α : Type} : (State → M (α × State)) → BfT M α
-/
#guard_msgs in #check mapMStateAnd

section sol!
def mapMState (f : State → M State) : BfT M Unit :=
  mapMStateAnd fun state => do
    return ((), ← f state)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.mapMState {M : Type → Type} [Monad M] (f : State → M State) : BfT M Unit
-/
#guard_msgs in #check mapMState

section sol!
def stateDoM (f : State → M α) : BfT M α :=
  mapMStateAnd fun state => do
    return (← f state, state)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.stateDoM {M : Type → Type} [Monad M] {α : Type} (f : State → M α) : BfT M α
-/
#guard_msgs in #check stateDoM

section sol!
def mapStateAnd (f : State → α × State) : BfT M α :=
  mapMStateAnd (return f ·)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.mapStateAnd {M : Type → Type} [Monad M] {α : Type} (f : State → α × State) : BfT M α
-/
#guard_msgs in #check mapStateAnd

section sol!
def mapState (f : State → State) : BfT M Unit :=
  mapMState (return f ·)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.mapState {M : Type → Type} [Monad M] (f : State → State) : BfT M Unit
-/
#guard_msgs in #check mapState

section sol!
def stateDo (f : State → α) : BfT M α :=
  stateDoM (return f ·)
end sol!
/-- info:
Zen.Train.Bf.Rt.BfT.stateDo {M : Type → Type} [Monad M] {α : Type} (f : State → α) : BfT M α
-/
#guard_msgs in #check stateDo



/-! Time for `Monad (BfT M)`! -/

section sol!
protected def pure (a : α) : BfT M α
| state => return .ok a state

protected def bind (code : BfT M α) (f : α → BfT M β) : BfT M β
| state => do
  match ← code state with
  | .ok a state => f a state
  | .error e state => return .error e state

instance instMonad : Monad (BfT M) where
  pure := BfT.pure
  bind := BfT.bind
end sol!



/-! And the appropriate `MonadLift` instance. -/

section sol!
instance instMonadLift : MonadLift M (BfT M) where
  monadLift m state := do
    let val ← m
    return .ok val state
end sol!



/-! Lifting/defining useful state manipulation functions. -/
section liftStateFunctions

def getCurr : BfT M Nat :=
  stateDo State.getCurr

def emit (n : Nat) : BfT M Unit :=
  mapState fun s => s.emit n

def getPos : BfT M Nat :=
  stateDo fun s => s.ptr

def getLoopLimit : BfT M (Option Nat) :=
  stateDo fun s => s.loopLimit

def withDbg (dbg : Bool) : BfT M Unit :=
  mapState fun s => s.withDbg dbg

def withCheck (check : Bool) : BfT M Unit :=
  mapState fun s => s.withCheck check

def withLoopLimit (loopLimit : Nat) : BfT M Unit :=
  mapState fun s => s.withLoopLimit loopLimit

def withNoLoopLimit : BfT M Unit :=
  mapState State.withNoLoopLimit

def handleOp (op : Ast.Op) : BfT M Unit :=
  mapState fun s => s.applyOp op

def isZeroCurr : BfT M Bool :=
  stateDo fun s => s.getCurr = 0

def drainInput : BfT M Nat :=
  mapStateAnd fun s => s.drainInput

def drainOutputs : BfT M (Array Nat) :=
  mapStateAnd fun s => s.drainOutputs

end liftStateFunctions



/-! Define the following:

- `handleCheck : Ast.Check → BfT M Unit`, self-explanatory;
- `handleSeff : Ast.Seff → BfT M Unit`: ignores `Seff.dbg`-s;
- `handleSeff ... : Ast.Seff → BfT M Unit`: handles `Seff.dbg`-s with `println!`.
-/

section sol!
def handleCheck : Ast.Check → BfT M Unit
| .chk exp msg => do
  let self ← getState
  if self.check then
    let val ← getCurr
    if h_ne : exp ≠ val then
      throwCheckFailed msg exp val h_ne

def handleSeff : Ast.Seff → BfT M Unit
| .out => do
  let val ← getCurr
  emit val
| .inp => do
  let input ← drainInput
  mapState fun s => s.mapCurr (𝕂 input)
| .dbg _msg =>
  return ()

def handleSeffIO [MonadLiftT IO M] : Ast.Seff → BfT M Unit
| .dbg msg => do
  if (←getState).dbg then
    liftM (println! msg)
| seff => handleSeff seff
end sol!

end BfT



/-! `Spec` instances! -/

protected instance NoIO [Monad M] : Spec (BfT M) where
  op := BfT.handleOp
  seff := BfT.handleSeff
  check := BfT.handleCheck
  getCurr := BfT.getCurr
  getLoopLimit := BfT.getLoopLimit
  throw := BfT.throw

protected instance IO [Monad M] [MonadLiftT IO M] : Spec (BfT M) :=
  {Rt.NoIO with seff := BfT.handleSeffIO}

/-- info:
done
memory: #[0, 2]
#[2]
-/
#guard_msgs in #eval do
  let ast := Ast.Test.val1
  let res := Rt.IO.justRun ast $ State.mk []
  match ← res with
  | .ok _ s =>
    println! "memory: {s.mem}"
    return s.outputs
  | .error e s =>
    println! "something went wrong, memory state is {s.mem}@{s.ptr}"
    IO.throwServerError e.toString



namespace Spec
variable [Monad M]

def justExe
  (S : Spec (BfT M)) (code : Ast) (ex : Extract α)
: BfT M α := do
  S.justRun code
  match ex.apply (← BfT.drainOutputs) with
  | .ok res => return res
  | .error e => S.throw e

def exe
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α) (config := Config.default)
: M (BfT.Res α) := do
  State.mk inputs (config := config) |> S.justExe code ex

def exe!
  [Inhabited α]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α) (config := Config.default)
: M α := do
  match ← S.exe code inputs ex config with
  | .ok res _ => return res
  | .error err _ => panic! err.toString
end Spec



/-- info: done #[2, 8] -/
#guard_msgs in #eval
  Rt.IO.exe! (M := IO) (Ast.Test.val1 ++ .mvr ++ .inp ++ .inc ++ .out) [7] .array


abbrev BfM :=
  BfT Id

abbrev BfIO :=
  BfT IO

end Rt



namespace Ast
variable
  [Inhabited α]
  (self : Ast) (inputs : List Nat) (ex : Rt.Extract α)

def evalTo : Rt.BfT.Res α :=
  Rt.NoIO.exe (M := Id) self inputs ex
def eval : Rt.BfT.Res (Array Nat) :=
  Rt.NoIO.exe (M := Id) self inputs .array

def evalTo! : α :=
  Rt.NoIO.exe! (M := Id) self inputs ex
def eval! : Array Nat :=
  Rt.NoIO.exe! (M := Id) self inputs .array

def evalIOTo : IO (Rt.BfT.Res α) :=
  Rt.IO.exe (M := IO) self inputs ex
def evalIO : IO (Rt.BfT.Res (Array Nat)) :=
  Rt.IO.exe (M := IO) self inputs .array

def evalIOTo! : IO α :=
  Rt.IO.exe! (M := IO) self inputs ex
def evalIO! : IO (Array Nat) :=
  Rt.IO.exe! (M := IO) self inputs .array
end Ast



/-! Let's do this. -/
namespace Std

export Ast (
  mvr mvl
  inc dec
  seq block
  seqN moveBy add sub
  out inp
  dbg chk
)

/-- Decreases the current cell, increase some other cell, come back. -/
def dec_inc (target : Int) : Ast :=
  seq #[dec, moveBy target, inc, moveBy (-target)]

/-- Moves the current cell to some other cell. -/
def moveValueBy : Int → Ast :=
  block ∘ dec_inc

/-- Outputs the current cells and the `i` cells on the right if `0 ≤ i`, on the left otherwise. -/
def emitCells (i : Int) : Ast :=
  let (mv, count) :=
    match i with
    | .ofNat n => (mvr, n)
    | .negSucc n => (mvl, n.succ)
  let mv_out := Ast.seq #[mv, out]
  seq #[ out, mv_out.seqN count ]

/-- info:
#[0, 0, 0, 7, 0, 0]
-/
#guard_msgs in #eval do
  let test : Ast := .seq #[
    chk 0 "fresh cell should store `0`",
    dbg "reading input",
    inp,
    dbg "moving 3 cells right",
    moveBy 3,
    chk 0 "fresh cell should store `0`",
    dbg "going back",
    moveBy (-3),
    dbg "moving previously read value by three",
    moveValueBy 3,
    chk 0 "current cell should store `0` after moving its value",
    dbg "emitting the 5 cells on the right of the current cell",
    emitCells 5
  ]
  test.eval! [7]
