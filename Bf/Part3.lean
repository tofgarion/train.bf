import Bf.Part2



/-! # Concretizing the runtime -/
namespace Zen.Train.Bf


structure Rt.Basic.Mem where
private mkRaw ::
  mem : Array Nat
  ptr : Fin mem.size

namespace Rt.Basic.Mem

def mk (capa : Nat := 123) : Mem where
  mem := Array.mkEmpty capa |>.push 0
  ptr := ⟨0, by simp⟩

variable (self : Mem)

def mapCurr (f : Nat → Nat) : Mem :=
  let val := f self.mem[self.ptr]
  let mem := self.mem.set self.ptr val
  let tmp : mem.size = self.mem.size :=
    by simp [mem]
  ⟨mem, tmp ▸ self.ptr⟩

def getCurr : Nat :=
  self.mem[self.ptr]

def mvl : Mem := {self with
  ptr := ⟨self.ptr - 1, Nat.lt_of_le_of_lt self.ptr.val.pred_le self.ptr.isLt⟩
}

def mvr : Mem :=
  if isLt : self.ptr.val + 1 < self.mem.size
  then { self with ptr := ⟨self.ptr.val + 1, isLt⟩ }
  else
    let mem := self.mem.push 0
    {self with mem, ptr := ⟨self.ptr.val + 1, by
      simp [mem, Array.size_push, Nat.succ_lt_succ]
    ⟩}

def applyOp : Ast.Op → Mem
| .mvr => self.mvr
| .mvl => self.mvl
| .inc => self.mapCurr Nat.succ
| .dec => self.mapCurr Nat.pred

end Rt.Basic.Mem



structure Rt.Basic.State extends Rt.Basic.Mem where
private mkRaw ::
  dbg : Bool
  check : Bool
  loopLimit : Option Nat
  inputs : List Nat
  outputs : Array Nat

namespace Rt.Basic.State

def mk (inputs : List Nat) (capa : Nat := 123) : State where
  toMem := Mem.mk capa
  dbg := true
  check := true
  loopLimit := some 123
  inputs := inputs
  outputs := #[]

private def liftMemFun (f : Mem → Mem) : State → State
| self => {self with toMem := f self.toMem}

variable (self : State)

def emit (n : Nat) : State :=
  {self with outputs := self.outputs.push n}

def drainInput : Nat × State :=
  match self.inputs with
  | [] => (0, self)
  | nxt::inputs => (nxt, {self with inputs})

def mapCurr f := liftMemFun fun m => m.mapCurr f
def applyOp o := liftMemFun fun m => m.applyOp o
def mvl := liftMemFun .mvl
def mvr := liftMemFun .mvr
def getCurr := self.toMem.getCurr

end Rt.Basic.State



inductive Rt.Extract : Type → Type 1
| unit : Extract Unit
| array : Extract (Array Nat)
| head? : Extract (Option Nat)
| head! : Extract Nat
| tryFold : α → (α → Nat → Except Rt.Error α) → Extract α

namespace Rt.Extract

protected abbrev Out (_ : Extract α) : Type := α

instance instCoeSort : CoeSort (Extract α) Type :=
  ⟨𝕂 α⟩

def fold (init : α) (f : α → Nat → α) : Extract α :=
  tryFold init (f · · |> .ok)


def apply : (self : Extract α) → Array Nat → Except Rt.Error α
| unit, _ => return ()
| array, a => return a
| head?, a =>
  if h : 0 < a.size
  then return a[0]
  else return none
| head!, a => do
  if h : 0 < a.size
  then return a[0]
  else .error <| .text "[bf] failed to extract output `head!`, no output available"
| tryFold init f, l => do
  let mut res := init
  for n in l do
    res ← f res n
  return res
  -- -- alternatively just
  -- l.foldlM f init

def apply! (self : Extract α) [Inhabited α] :=
  (self.apply · |>.toOption |>.get!)



/-- String extraction, where non-char values are interpreted as separators. -/
def string : Extract (Array String) :=
  fold #[] combine
where
  combine stringArray n :=
    let c := Char.ofNat n
    if c.val = 0 then
      if h : stringArray.size ≠ 0 then
        if let "" := stringArray.last
        then stringArray
        else stringArray.push ""
      else
        stringArray
    else
      let (curr, stringArray) :=
        if h : stringArray.size ≠ 0
        then stringArray.pop'
        else ("", stringArray)
      curr.push c |> stringArray.push

/-- info:
first result:
  `I 🖤 猫`
second result:
  `I 🖤 猫`
  `next bit`
third result:
  `I 🖤 猫`
  `next bit`
  `and then`
  `finally`
-/
#guard_msgs in #eval do
  let chars := "I 🖤 猫".data.map Char.toNat
  println! "first result:"
  for bit in string.apply! chars.toArray do
    println! "  `{bit}`"
  let chars :=
    chars ++ [0] ++ ("next bit".data.map Char.toNat)
  println! "second result:"
  for bit in string.apply! chars.toArray do
    println! "  `{bit}`"
  let chars :=
    chars
    ++ [2013420531] ++ ("and then".data.map Char.toNat)
    ++ [20130531] ++ [52016027] ++ ("finally".data.map Char.toNat)
  println! "third result:"
  for bit in string.apply! chars.toArray do
    println! "  `{bit}`"

def sum (init : Nat := 0) : Extract Nat :=
  fold init Nat.add

/-- info:
- sum #[0, 1, 2, 3] => 6
- sum #[] => 0
-/
#guard_msgs in #eval do
  let data := #[0, 1, 2, 3]
  println! "- sum {data} => {sum.apply! data}"
  println! "- sum #[] => {sum.apply! #[]}"

end Rt.Extract



structure Rt.Extract' : Type 1 where
private mkRaw ::
  Out : Type
  isInhabitedOut : Inhabited Out
  isToExprOut : Lean.ToExpr Out
  extract : Extract Out

namespace Rt.Extract'
def mk [Inhabited α] [Lean.ToExpr α] (extract : Extract α) : Extract' where
  Out := α
  isInhabitedOut := inferInstance
  isToExprOut := inferInstance
  extract := extract

instance instInhabited : Inhabited Extract' where
  default := mk Extract.array

variable (self : Extract')

instance instInhabitedOut : Inhabited self.Out := self.isInhabitedOut
instance instToExprOut : Lean.ToExpr self.Out := self.isToExprOut

def apply := self.extract.apply
def apply! := self.extract.apply!
end Rt.Extract'



def Rt.Extract.hideType
  [Inhabited α] [Lean.ToExpr α]
  (self : Extract α)
: Extract' :=
  Extract'.mk self




inductive Rt.BfT.Res (α : Type)
| ok : α → Basic.State → Res α
| error : Error → Basic.State → Res α

namespace Rt.BfT.Res
instance instFunctor : Functor Res where
  map
    | f, ok val s => ok (f val) s
    | _, error e s => error e s

def map (f : α → β) (self : Res α) :=
  f <$> self
end Rt.BfT.Res

abbrev Rt.BfT (M : Type → Type) (α : Type) :=
  Basic.State → M (BfT.Res α)

namespace Rt.BfT
variable {M : Type → Type} [Monad M]

def fail : Error → BfT M α :=
  (.error · · |> pure)

def loopLimitFail : (limit : Nat) → (count : Nat) → limit < count → BfT M α :=
  (.loopLimit · · · |> fail)

def checkFail (msg : String) (exp val : Nat) (h_ne : exp ≠ val) : BfT M α :=
  fail <| .checkFailed msg exp val h_ne

def getState : BfT M Basic.State
| state => return .ok state state

def setState : Basic.State → BfT M Unit
| state, _ => return .ok () state

def mapMStateAnd : (Basic.State → M (α × Basic.State)) → BfT M α
| f, state => do
  let (res, state) ← f state
  return .ok res state

def mapMState (f : Basic.State → M Basic.State) : BfT M Unit :=
  mapMStateAnd fun state => do
    return ((), ← f state)

def stateDoM (f : Basic.State → M α) : BfT M α :=
  mapMStateAnd fun state => do
    return (← f state, state)

def mapStateAnd (f : Basic.State → α × Basic.State) : BfT M α :=
  mapMStateAnd (return f ·)

def mapState (f : Basic.State → Basic.State) : BfT M Unit :=
  mapMState (return f ·)

def stateDo (f : Basic.State → α) : BfT M α :=
  stateDoM (return f ·)



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

instance instMonadLift : MonadLift M (BfT M) where
  monadLift m state := do
    let val ← m
    return .ok val state



open Basic (State)

def getCurr : BfT M Nat :=
  stateDo State.getCurr

def emit (n : Nat) : BfT M Unit :=
  mapState fun s => s.emit n

def getPos : BfT M Nat :=
  stateDo fun s => s.ptr

def getLoopLimit : BfT M (Option Nat) :=
  stateDo fun s => s.loopLimit

def withDbg (dbg : Bool) : BfT M Unit :=
  mapState ({· with dbg})

def withCheck (check : Bool) : BfT M Unit :=
  mapState ({· with check})

def withLoopLimit (loopLimit : Nat) : BfT M Unit :=
  mapState ({· with loopLimit})

def withNoLoopLimit : BfT M Unit :=
  mapState ({· with loopLimit := none})

def handleOp (op : Ast.Op) : BfT M Unit :=
  mapState fun s => s.applyOp op

def isZeroCurr : BfT M Bool :=
  stateDo fun s => s.getCurr = 0

def drainInput : BfT M Nat :=
  mapStateAnd fun s => s.drainInput

def drainOutputs : BfT M (Array Nat) :=
  mapStateAnd fun s => (s.outputs, {s with outputs := Array.mkEmpty 123})

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

def handleCheck : Ast.Check → BfT M Unit
| .chk exp msg => do
  let self ← getState
  if self.check then
    let val ← getCurr
    if h_ne : exp ≠ val then
      checkFail msg exp val h_ne


instance instSpec : Spec (BfT M) where
  op := handleOp
  seff := handleSeff
  check := handleCheck
  isZeroCurr := isZeroCurr
  getCurr := getCurr
  getLoopLimit := getLoopLimit
  fail := fail

instance instSpecIO [MonadLiftT IO M] : Spec (BfT M) :=
  {instSpec with seff := handleSeffIO}

/-- info: done #[2] -/
#guard_msgs in #eval do
  let ast := Ast.Test.val1
  let blah := instSpecIO.runCode ast $ Rt.Basic.State.mk []
  match ← blah with
  | .ok _ s => return s.outputs
  | .error e s =>
    println! "something went wrong, memory state is {s.mem}@{s.ptr}"
    IO.throwServerError e.toString




def run
  (S : Spec (BfT M)) (code : Ast) (ex : Extract α)
: BfT M α := do
  S.runCode code
  match ex.apply (← drainOutputs) with
  | .ok res => return res
  | .error e => S.fail e

def justRun
  [Inhabited α]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α)
: M (BfT.Res α) := do
  Basic.State.mk inputs |> run S code ex

def justRun!
  [Inhabited α]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α)
: M α := do
  match ← justRun S code inputs ex with
  | .ok res _ => return res
  | .error err _ => panic! err.toString

def justRunToExpr
  [Inhabited α] [Lean.ToExpr α]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α)
: M (BfT.Res Lean.Expr) := do
  let res ← justRun S code inputs ex
  return Lean.ToExpr.toExpr <$> res

end Rt.BfT

namespace Rt.NoIO
variable {M : Type → Type} [Monad M] [MonadLiftT IO M] [Inhabited α] [Lean.ToExpr α]
  (code : Ast) (inputs : List Nat) (ex : Extract α)

def run : BfT M α :=
  Rt.BfT.run Rt.BfT.instSpec code ex
def justRun : M (Rt.BfT.Res α) :=
  Rt.BfT.justRun Rt.BfT.instSpec code inputs ex
def justRun! : M α :=
  Rt.BfT.justRun! Rt.BfT.instSpec code inputs ex
def justRunToExpr : M (Rt.BfT.Res Lean.Expr) :=
  Rt.BfT.justRunToExpr Rt.BfT.instSpec code inputs ex
end Rt.NoIO

namespace Rt.IO
variable {M : Type → Type} [Monad M] [MonadLiftT IO M] [Inhabited α] [Lean.ToExpr α]
  (code : Ast) (inputs : List Nat) (ex : Extract α)

def run : BfT M α :=
  Rt.BfT.run Rt.BfT.instSpecIO code ex
def justRun : M (Rt.BfT.Res α) :=
  Rt.BfT.justRun Rt.BfT.instSpecIO code inputs ex
def justRun! : M α :=
  Rt.BfT.justRun! Rt.BfT.instSpecIO code inputs ex
def justRunToExpr : M (Rt.BfT.Res Lean.Expr) :=
  Rt.BfT.justRunToExpr Rt.BfT.instSpecIO code inputs ex
end Rt.IO



/-- info: done #[2, 8] -/
#guard_msgs in #eval
  Rt.IO.justRun! (M := IO) (Ast.Test.val1 ++ .mvr ++ .inp ++ .inc ++ .out) [7] .array


abbrev Rt.BfM :=
  BfT Id

abbrev Rt.BfIO :=
  BfT IO



namespace Ast
variable
  [Inhabited α]
  (self : Ast) (inputs : List Nat) (ex : Rt.Extract α)

def evalTo : Rt.BfT.Res α :=
  Rt.NoIO.justRun (M := Id) self inputs ex
def eval : Rt.BfT.Res (Array Nat) :=
  Rt.NoIO.justRun (M := Id) self inputs .array

def evalTo! : α :=
  Rt.NoIO.justRun! (M := Id) self inputs ex
def eval! : Array Nat :=
  Rt.NoIO.justRun! (M := Id) self inputs .array

def evalIOTo : IO (Rt.BfT.Res α) :=
  Rt.IO.justRun (M := IO) self inputs ex
def evalIO : IO (Rt.BfT.Res (Array Nat)) :=
  Rt.IO.justRun (M := IO) self inputs .array

def evalIOTo! : IO α :=
  Rt.IO.justRun! (M := IO) self inputs ex
def evalIO! : IO (Array Nat) :=
  Rt.IO.justRun! (M := IO) self inputs .array
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
