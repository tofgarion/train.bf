import Bf.Part2



/-! # Abstract runtime: non-trivial code and monads -/
namespace Zen.Train.Bf



private def alignRight (width : Nat) (s : String) (c := ' ') : String :=
  if width > s.length then Id.run do
    let mut pref := ""
    for _ in [0 : width - s.length] do
      pref := pref.push c
    pref ++ s
  else s

/-- info: `---` `--1` `-12` `123` `1234` -/
#guard_msgs in #eval do
  println! "`{alignRight 3 "" '-'}`"
  println! "`{alignRight 3 "1" '-'}`"
  println! "`{alignRight 3 "12" '-'}`"
  println! "`{alignRight 3 "123" '-'}`"
  println! "`{alignRight 3 "1234" '-'}`"

namespace Rt.Mem
variable (self : Mem)

/-! Let's warm up on monads: write `Rt.Mem.prettyMemLines` using
- `Id.run do`
- `alignRight` above
- a `for` loop on `self.mem`.
-/
def prettyMemLines (pref := "") : Array String := Id.run do
  let cellIdxWith :=
    toString self.mem.size.pred |>.length |> (. + 2)
  let mut lines := Array.mkEmpty self.mem.size
  let mut idx   := 0
  for val in self.mem do
    let idxStr :=
      if idx = self.ptr.val
      then s!"*{idx}*"
      else s!"{idx} "
    lines := lines.push s!"{pref}{alignRight cellIdxWith idxStr} ↦ {val}"
    idx := idx + 1
  lines

#eval do
  for line in Mem.mk |>.mvr |>.setCurr 3 |>.prettyMemLines "> " do
    println! line

def prettyMem (pref := "") : String :=
  self.prettyMemLines pref |>.foldl
    (fun | "", l => l | s, l => s ++ "\n" ++ l)
    ""

def prettyPrint (pref := "") : IO Unit := do
  for line in self.prettyMemLines do
    println! "{pref}{line}"

/-- info:
>  0  ↦ 0
> *1* ↦ 7
>  2  ↦ 10
----
>   0  ↦ 0
>   1  ↦ 7
>   2  ↦ 10
>   3  ↦ 0
>   4  ↦ 0
>   5  ↦ 0
>   6  ↦ 0
>   7  ↦ 0
>   8  ↦ 0
>   9  ↦ 0
> *10* ↦ 9
-/
#guard_msgs in #eval do
  let mut mem := mk |>.mvr |>.setCurr 7 |>.mvr |>.setCurr 10 |>.mvl
  mem.prettyPrint "> "
  for _ in [0:9] do
    mem := mem.mvr
  mem := mem.setCurr 9
  println! "----"
  mem.prettyPrint "> "

end Rt.Mem





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
structure Spec (Mon : Type → Type u) where
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

def isZeroCurr (self : Spec Mon) : Mon Bool :=
  --      vvv~~~~~ `Functor.map`, comes for free as `Monad Mon` implies `Functor Mon`
  (· = 0) <$> self.getCurr
  -- or do let val ← self.getCurr return val = 0

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
  op operator := do
    let state ← get
    set (state.applyOp operator)
  seff
  | .out => fun s => return ((), s.emit s.getCurr)
  | .inp => fun s =>
    let (val, s) := s.drainInput
    return ((), s.mapCurr (𝕂 val))
  | .dbg msg => println! msg
  | .dump => do
    let state ← get
    println! "memory:\n{state.prettyMem "| "}"
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

which you could also write as follows (less idiomatic though)

```
mutual
def runWithStack ... :=
  ...
def goUp ... :=
  ...
end
```
-/

partial
def runWithStack [Monad Mon] (self : Spec Mon) (stack : Stack) :  Ast → Mon Unit
| .op operation => do
  self.op operation
  goUp stack
| .seff effect => do
  self.seff effect
  goUp stack
| .check condition => do
  self.check condition
  goUp stack
| .seq seq_array =>
  if h_size : 0 < seq_array.size then
    let frame := Frame.seq seq_array ⟨ 0, h_size ⟩
    let stack := frame :: stack
    self.runWithStack stack (seq_array.get ⟨ 0, h_size ⟩)
  else
    goUp stack
| .block body => do
  let val ← self.getCurr
  if val = 0
  then goUp stack
  else
    let frame := Frame.block val 0 body
    let stack := frame::stack
    self.runWithStack stack body
where
  -- look at stack and find the next thing to do
  goUp : Stack → Mon Unit
  | []                           => return ()
  | (Frame.seq arr idx) :: stack =>
    if h_size : idx + 1 < arr.size then
      let idx' : Fin arr.size := ⟨ idx + 1, h_size ⟩
      let frame := Frame.seq arr idx'
      let stack := frame :: stack
      self.runWithStack stack (arr.get ⟨ idx', h_size ⟩)
    else
      goUp stack
  | Frame.block oldVal count body :: stack => do
    let val ← self.getCurr
    if val = 0 then
      goUp stack
    else
      let count := if oldVal ≤ val then count + 1 else count
      if let some limit ← self.getLoopLimit then
        if h_err : limit < count then
          self.throw <| Error.loopLimit limit count h_err
      let frame := Frame.block val count body
      let stack := frame :: stack
      self.runWithStack stack body

/-- info:
Zen.Train.Bf.Rt.Spec.runWithStack.{u} {Mon : Type → Type u} [Monad Mon] (self : Spec Mon) (stack : Stack) :
  Ast → Mon Unit
-/
#guard_msgs in #check runWithStack



@[specialize 1 2 self, always_inline, inline]
abbrev justRun (self : Spec Mon) : Ast → Mon Unit :=
  self.runWithStack []



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

abbrev BfT (M : Type → Type) (α : Type) : Type :=
  State → M (Except Error α × State)



/-! Great, make sure you have my version now. -/

namespace BfT.Res
/-! Is `BfT.Res` a (reasonable) monad?

Is there a `bind`-like operation that would make sense here?
-/

-- todo 🙀
end BfT.Res



namespace BfT
variable {M : Type → Type} [Monad M]


/-! Let's write a bunch of functions 🐙 -/

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.throw {M : Type → Type} [Monad M] {α : Type} : Error → BfT M α
-/
#guard_msgs in #check throw

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.throwLoopLimit {M : Type → Type} [Monad M] {α : Type} (limit count : Nat) : limit < count → BfT M α
-/
#guard_msgs in #check throwLoopLimit

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.throwCheckFailed {M : Type → Type} [Monad M] {α : Type} (msg : String) (exp val : Nat)
  (h_ne : exp ≠ val) : BfT M α
-/
#guard_msgs in #check throwCheckFailed

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.getState {M : Type → Type} [Monad M] : BfT M State
-/
#guard_msgs in #check getState

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.setState {M : Type → Type} [Monad M] : State → BfT M Unit
-/
#guard_msgs in #check setState

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.mapMStateAnd {M : Type → Type} [Monad M] {α : Type} : (State → M (α × State)) → BfT M α
-/
#guard_msgs in #check mapMStateAnd

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.mapMState {M : Type → Type} [Monad M] (f : State → M State) : BfT M Unit
-/
#guard_msgs in #check mapMState

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.stateDoM {M : Type → Type} [Monad M] {α : Type} (f : State → M α) : BfT M α
-/
#guard_msgs in #check stateDoM

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.mapStateAnd {M : Type → Type} [Monad M] {α : Type} (f : State → α × State) : BfT M α
-/
#guard_msgs in #check mapStateAnd

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.mapState {M : Type → Type} [Monad M] (f : State → State) : BfT M Unit
-/
#guard_msgs in #check mapState

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.BfT.stateDo {M : Type → Type} [Monad M] {α : Type} (f : State → α) : BfT M α
-/
#guard_msgs in #check stateDo



/-! Time for `Monad (BfT M)`! -/

-- todo 🙀



/-! And the appropriate `MonadLift` instance. -/

-- todo 🙀



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

-- todo 🙀

end BfT



/-! `Spec` instances! -/

@[specialize]
protected instance NoIO [Monad M] : Spec (BfT M) where
  op := BfT.handleOp
  seff := BfT.handleSeff
  check := BfT.handleCheck
  getCurr := BfT.getCurr
  getLoopLimit := BfT.getLoopLimit
  throw := BfT.throw

@[specialize]
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

@[specialize]
def justExe
  (S : Spec (BfT M)) (code : Ast) (ex : Extract α)
: BfT M α := do
  S.justRun code
  match ex.apply (← BfT.drainOutputs) with
  | .ok res => return res
  | .error e => S.throw e

@[specialize]
def exe
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α) (config := Config.default)
: M (BfT.Res α) := do
  State.mk inputs (config := config) |> S.justExe code ex

@[specialize]
def exe!
  [Inhabited α]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α) (config := Config.default)
: M α := do
  match ← S.exe code inputs ex config with
  | .ok res _ => return res
  | .error err _ => panic! err.toString

@[specialize]
def exeIO!
  [Inhabited α] [MonadLiftT IO M]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α) (config := Config.default)
: M α := do
  match ← S.exe code inputs ex config with
  | .ok res _ => return res
  | .error err _ => IO.throwServerError err.toString
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
  (self : Ast) (inputs : List Nat) (ex : Rt.Extract α) (config := Rt.Config.default)

def evalTo : Rt.BfT.Res α :=
  Rt.NoIO.exe (M := Id) self inputs ex config
def eval : Rt.BfT.Res (Array Nat) :=
  Rt.NoIO.exe (M := Id) self inputs .array config

def evalTo! : α :=
  Rt.NoIO.exe! (M := Id) self inputs ex config
def eval! : Array Nat :=
  Rt.NoIO.exe! (M := Id) self inputs .array config

def evalIOTo : IO (Rt.BfT.Res α) :=
  Rt.IO.exe (M := IO) self inputs ex config
def evalIO : IO (Rt.BfT.Res (Array Nat)) :=
  Rt.IO.exe (M := IO) self inputs .array config

def evalIOTo! : IO α :=
  Rt.IO.exeIO! (M := IO) self inputs ex config
def evalIO! : IO (Array Nat) :=
  Rt.IO.exeIO! (M := IO) self inputs .array config
end Ast



/-! Let's do this. -/
namespace Std

export Ast (
  mvr mvl
  inc dec
  seq block blockSeq
  seqN moveBy add sub
  out inp
  dbg dump chk
)

def loop := block
def loopSeq := blockSeq

/-- Sets the current cell to zero. -/
def set0 : Ast :=
  loop dec

/-- Decreases the current cell, increase some other cell, come back. -/
def decInc (target : Int) : Ast :=
  seq #[dec, moveBy target, inc, moveBy (-target)]

/-- Adds (subtracts) `i : Int` to the current cell if `0 ≤ i` (`i < 0`). -/
def addInt : Int → Ast
| .ofNat n => add n
| .negSucc n => sub n.succ

/-- Moves the current cell to some other cell. -/
def moveValueBy : Int → Ast :=
  loop ∘ decInc

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



/-- Runs `ast` `n` times, current cell is used as the counter and must be zero.

- `ast` runs after an `Ast.mvr`, *i.e.* no need to move out of the counter.
-/
def doFor (n : Nat) (ast : Ast) : Ast := .seq #[
  add n,
  loop (dec.chain ast)
]

/-- Adds current value to a relative `target`, draining the current value. -/
def addMoveBy (target : Nat) : Ast :=
  loopSeq #[ dec, moveBy target, inc, moveBy (-target) ]

/-- Adds current value to a relative `target`, preserves the current value.

Uses a temporary cell, defaults to `target + 1`
-/
def addCopyBy (target : Nat) (tmp := target + 1) : Ast :=
  seq #[
    loop (decInc tmp),
    moveBy tmp,
    loopSeq #[
      dec, -- decrease `tmp`
      mvl, inc, -- increase `target`
      moveBy (-target), inc, -- increase original cell
      moveBy tmp -- back to `tmp`
    ],
    moveBy (-tmp) -- back to original cell
  ]

def fib : Ast :=
  seq #[ inp, pure, out ]
where
  /-- Replaces the current cell value `v` by `fibonacci[v+1]`. -/
  pure : Ast := seq #[
    -- mem[0]: decrementing counter, originaly `v`
    -- mem[1]: previous value
    -- mem[2]: current value
    -- mem[3]: used for copies
    dbg "starting",
    mvr, inc, -- mem[1] = 1
    mvr, inc, -- mem[2] = 1
    moveBy (-2), -- back to mem[0]
    dec,
    -- if mem[0] was `0` or `1` we're done, otherwise compute next fib number
    loopSeq #[
      dec, -- decrement counter (mem[0])
      dbg "starting outter loop (counter decremented)", dump,
      mvr, moveValueBy 2, -- move previous value to mem[3]
      mvr, loopSeq #[
        -- add current fib-value (mem[2]) to old fib-value (mem[1] = `0`) and mem[3]
        dec, mvl, inc, moveBy 2, inc, mvl
      ], -- current fib-value (mem[2]) is now `0`
      dbg "before moving current value", dump,
      mvr, moveValueBy (-1),
      moveBy (-3), -- back to counter (mem[0])
      dbg "looping back (maybe)"
    ],
    chk 0 "counter should be 0",
    dbg "done with main loop",
    -- result is two cells right, move it to `mem[0]`
    moveBy 2, moveValueBy (-2),
    -- cleanup, set mem[1] `0`
    mvl, set0,
    -- -- go back to original cell
    mvl,
    dbg "done"
  ]

/-- info:
computing `fib 4`
starting
starting outter loop (counter decremented)
memory:
| *0* ↦ 2
|  1  ↦ 1
|  2  ↦ 1
before moving current value
memory:
|  0  ↦ 2
|  1  ↦ 1
| *2* ↦ 0
|  3  ↦ 2
looping back (maybe)
starting outter loop (counter decremented)
memory:
| *0* ↦ 1
|  1  ↦ 1
|  2  ↦ 2
|  3  ↦ 0
before moving current value
memory:
|  0  ↦ 1
|  1  ↦ 2
| *2* ↦ 0
|  3  ↦ 3
looping back (maybe)
starting outter loop (counter decremented)
memory:
| *0* ↦ 0
|  1  ↦ 2
|  2  ↦ 3
|  3  ↦ 0
before moving current value
memory:
|  0  ↦ 0
|  1  ↦ 3
| *2* ↦ 0
|  3  ↦ 5
looping back (maybe)
done with main loop
done
#[5]
-/
#guard_msgs in #eval do
  let fib := fib
  let n := 4
  println! "computing `fib {n}`"
  fib.evalIO! [n]

/-- info:
fib[0] = 1
fib[1] = 1
fib[2] = 2
fib[3] = 3
fib[4] = 5
fib[5] = 8
fib[6] = 13
fib[7] = 21
-/
#guard_msgs in #eval do
  let fib := seq #[
    out, fib.pure, out, -- compute `fib 0` first
    -- loop :
    -- - read an input `i`
    -- - if zero then stop
    -- - else outputs the input, run `fib i` and outputs the result
    inp, loopSeq #[ out, fib.pure, out, inp ]
  ]
  let outputs ←
    fib.evalIOTo! [1, 2, 3, 4, 5, 6, 7] .array (config := .allOff)
  let mut num := none
  for val in outputs do
    if let some n := num then
      println! "fib[{n}] = {val}"
      num := none
    else
      num := some val
