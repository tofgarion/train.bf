import Bf.Part1



/-! # Abstract runtime: non-trivial code and monads -/
namespace Zen.Train.Bf



inductive Ast.Frame
| seq : (array : Array Ast) → Fin array.size → Frame
| block (oldVal : Nat) (count : Nat) : Ast → Frame

abbrev Ast.Frames := List Ast.Frame



inductive Rt.Error
| text : String → Error
| loopLimit : (limit : Nat) → (count : Nat) → limit < count → Error
| checkFailed : String → (exp : Nat) → (val : Nat) → exp ≠ val → Error

namespace Rt.Error

def toString : Rt.Error → String
| text msg => s!"error: {msg}"
| loopLimit limit count _ => s!"\
  potential infinite loop detected \
  after {count} non-decreasing iterations \
  (limit is {limit})\
"
| checkFailed msg exp val _ =>
  s!"value check failed, expected `{exp}`, got `{val}`: {msg}"

instance instToString : ToString Error :=
  ⟨toString⟩
end Rt.Error



class Rt.Spec (Mon : Type → Type u) where
  op : Ast.Op → Mon Unit
  seff : Ast.Seff → Mon Unit
  check : Ast.Check → Mon Unit
  isZeroCurr : Mon Bool
  getCurr : Mon Nat
  getLoopLimit : Mon $ Option Nat
  fail : Rt.Error → Mon α



section
variable
  ⦃Mon : Type → Type u⦄
  [Monad Mon]
  [R : Rt.Spec Mon]

partial def Ast.runWith (stack : Ast.Frames) : Ast → Mon Unit
| .op o => do
  R.op o
  goUp stack
| .seff s => do
  R.seff s
  goUp stack
| .check c => do
  R.check c
  goUp stack
| .block b => do
  if ← R.isZeroCurr then goUp stack else
    let val ← R.getCurr
    b.runWith (.block val 0 b :: stack)
| .seq s =>
  if h : 0 < s.size then
    let stack := .seq s ⟨0, h⟩ :: stack
    s[0].runWith stack
  else goUp stack
where
  goUp : Ast.Frames → Mon Unit
  | [] => return ()
  | .seq s idx :: stack =>
    let idx := idx.val + 1
    if h : idx < s.size then
      let stack := .seq s ⟨idx, h⟩ :: stack
      s[idx].runWith stack
    else
      goUp stack
  | .block oldVal count body :: stack => do
    if ← R.isZeroCurr then goUp stack else
      let val ← R.getCurr
      let count := if val < oldVal then count else count.succ
      let loopLimit ← R.getLoopLimit
      if let some limit := loopLimit then
        if h_lt : limit < count then
          Rt.Error.loopLimit limit count h_lt
          |> R.fail
      body.runWith (.block val count body :: stack)

partial def Ast.runWithDbg [MonadLiftT IO Mon] (stack : Ast.Frames) : Ast → Mon Unit
| .op o => do
  println! "op {o}"
  R.op o
  goUp stack
| .seff s => do
  println! "seff {s}"
  R.seff s
  goUp stack
| .check c => do
  println! "check {c}"
  R.check c
  goUp stack
| .block b => do
  println! "entering block"
  if ← R.isZeroCurr then goUp stack else
    let val ← R.getCurr
    b.runWithDbg (.block val 0 b :: stack)
| .seq s => do
  println! "entering sequence"
  if h : 0 < s.size then
    let stack := .seq s ⟨0, h⟩ :: stack
    println! "-> {s[0]}"
    s[0].runWithDbg stack
  else
    println! "empty sequence, going up"
    goUp stack
where
  goUp : Ast.Frames → Mon Unit
  | [] => return ()
  | .seq s idx :: stack => do
    let idx := idx.val + 1
    if h : idx < s.size then
      let stack := .seq s ⟨idx, h⟩ :: stack
      println! "going down ({stack.length})"
      s[idx].runWithDbg stack
    else
      println! "going up ({stack.length})"
      goUp stack
  | .block oldVal count body :: stack => do
    println! "going up block"
    if ← R.isZeroCurr then goUp stack else
      let val ← R.getCurr
      let count := if val < oldVal then count else count.succ
      let loopLimit ← R.getLoopLimit
      if let some limit := loopLimit then
        if h_lt : limit < count then
          Rt.Error.loopLimit limit count h_lt
          |> R.fail
      body.runWithDbg (.block val count body :: stack)


abbrev Rt.Spec.runCode : Ast → Mon Unit :=
  Ast.runWith []
end


structure Rt : Type 1 where
  Mon : Type → Type
  instMonad : Monad Mon
  instSpec : Rt.Spec Mon

namespace Rt
variable (self : Rt)

/-! Make internal instances visible. -/

instance instMonadMon : Monad self.Mon := self.instMonad
instance instSpecMon : Spec self.Mon := self.instSpec

/-- Runs an ast on some runtime. -/
def run (a : Ast) : self.Mon Unit :=
  a.runWith []

end Rt

def Ast.runIn : (R : Rt) → Ast → R.Mon Unit :=
  Rt.run
