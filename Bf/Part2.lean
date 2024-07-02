import Bf.Part1



/-! # Runtime

## Loop limit

We're going to have a potentially infinite loop detection mechanism. So let's discuss that first.

As we execute `Ast` code, we will find `Ast.block`-s causing us to run their bodies (potientially)
multiple times. As we do this, for each block we (re-)execute we will maintain two important pieces
of information.

- `oldVal`: the cell value used for the non-zero check the last time we entered this block;
- `count`: the number of times the cell value we checked was **not** smaller than the old value.

For instance:

| current cell |           comment            | `oldVal` | `count` |
| -----------: | :--------------------------: | -------: | ------: |
|         `15` |        entering block        |     `15` |     `0` |
|         `10` | `10 < 15`, `count` unchanged |     `10` |     `0` |
|         `11` | `11 ≥ 10`, `count` increased |     `11` |     `1` |
|         `11` | `11 ≥ 11`, `count` increased |     `11` |     `2` |
|          `7` |          you get it          |      `7` |     `2` |
|          `2` |             ...              |      `2` |     `2` |
|          `0` |             done             |     none |    none |

The actual runtime will have an optional loop limit that will throw an error if `count` becomes
greater than that limit (if any).
-/
namespace Zen.Train.Bf.Rt



/-- Errors that running brainfuck code can throw. -/
inductive Error
/-- General-purpose string error. -/
| text : String → Error
/-- Loop limit reached, see module-level documentation for details. -/
| loopLimit : (limit : Nat) → (count : Nat) → limit < count → Error
/-- A failed `Ast.check`.

Stores the check's message, its expected value, the actual value, and a proof that they are
different.
-/
| checkFailed : String → (exp : Nat) → (val : Nat) → exp ≠ val → Error

namespace Error

protected def toString : Error → String
| text msg => s!"{msg}"
| loopLimit limit count _ => s!"\
  potential infinite loop detected \
  after {count} non-decreasing iterations \
  (limit is {limit})\
"
| checkFailed msg exp val _ =>
  s!"value check failed, expected `{exp}`, got `{val}`: {msg}"

instance instToString : ToString Error :=
  ⟨Error.toString⟩

end Error



/-! Time to do something!

Define `Mem` which is just our basic brainfuck memory. It stores two things:

- the actualy memory as an `Array Nat`;
- a pointer to the current cell.

I'm not giving you the type for the pointer. Just know that you will probably want to use the
following functions at some point.
-/
#check Array.get
#check Array.set

/-! And no, you're not allowed to use those. -/
#check Array.get!
#check Array.set!

/-! Also, please make the default constructor private with `private <ident> ::` between the `where`
and the fields:

```lean
structure Mem where
private mkRaw ::
  <fields>
```
-/


structure Mem where
private mkRaw ::
  mem : Array Nat
  ptr : Fin mem.size


namespace Mem

/-!
**NB**: remember that autocompletion is your friend, and so is Lean's documentation:

- <https://leanprover-community.github.io/mathlib4_docs>


Write the following function, its semantics should be straightforward from its signature.
-/

/-!
**NB**: when you need to prove something simple, try `by simp` in case it works.
-/

def mk (capacity : Nat := 123) : Mem where
  mem := Array.mkEmpty capacity |>.push 0
  ptr := Fin.mk 0 (by simp)

/-- info: Zen.Train.Bf.Rt.Mem.mk (capacity : Nat := 123) : Mem -/
#guard_msgs in #check mk


instance instInhabited : Inhabited Mem := ⟨mk⟩


variable (self : Mem)

def mapCurr (f : Nat → Nat) : Mem :=
  let val := f self.mem[self.ptr]
  let mem := self.mem.set self.ptr val
  let tmp : mem.size = self.mem.size :=
    by simp [mem]
  ⟨mem, tmp ▸ self.ptr⟩

def setCurr (val : Nat) : Mem :=
  self.mapCurr (𝕂 val)

def getCurr : Nat :=
  self.mem[self.ptr]

/-- info: Zen.Train.Bf.Rt.Mem.getCurr (self : Mem) : Nat -/
#guard_msgs in #check getCurr



/-! Note: `Ast.mvl` does nothing if we're pointing to the first cell of the array. (Maybe look at
what `Nat` subtraction does.)

Also, for no reason at all, maybe take a look at these.
-/
#checkout Nat.lt_of_le_of_lt
#checkout Nat.pred_le

def mvl : Mem := {
  self with
    ptr := ⟨
      self.ptr - 1,
      Nat.lt_of_le_of_lt (n := self.ptr - 1) (m := self.ptr) (k := self.mem.size)
        (Nat.pred_le self.ptr) (self.ptr.isLt)
    ⟩
}

/-- info: Zen.Train.Bf.Rt.Mem.mvl (self : Mem) : Mem -/
#guard_msgs in #check mvl



/-! This next one is more advanced, take a look but we go over it together.

We will use the following two theorems though, you can check them out.
-/
#checkout Array.size_push
#checkout Nat.succ_lt_succ

def mvr : Mem :=
  if h_succ_ptr : self.ptr.val + 1 < self.mem.size then
    { self with ptr := ⟨ self.ptr.val + 1, h_succ_ptr ⟩ }
  else
    let mem := self.mem.push 0
    { self with
      mem
      ptr := ⟨
        self.ptr.val + 1,
        by simp [mem, Nat.succ_lt_succ]
      ⟩
    }

/-- info: Zen.Train.Bf.Rt.Mem.mvr (self : Mem) : Mem -/
#guard_msgs in #check mvr



def applyOp : Ast.Op → Mem
| .mvr => self.mvr
| .mvl => self.mvl
| .inc => self.mapCurr Nat.succ
| .dec => self.mapCurr Nat.pred

end Mem



structure Config where
  /-- If false, ignore debug messages. -/
  dbg : Bool
  /-- If false, ignore checks. -/
  check : Bool
  /-- Optional loop limit, see module-level documentation. -/
  loopLimit : Option Nat

namespace Config
protected def default (dbg := true) (check := true) (loopLimit := some 123) : Config :=
  { dbg, check, loopLimit }

def allOff := Config.default false false none

instance instInhabited : Inhabited Config where
  default := Config.default
end Config



/-- The full state, extends `Mem` with some configuration and the inputs/outputs. -/
structure State extends Mem, Config where
private mkRaw ::
  inputs : List Nat
  outputs : Array Nat
deriving Inhabited

#check State.toMem
#check State.toConfig

namespace State

def mk (inputs : List Nat) (capa : Nat := 123) (config : Config := default) : State where
  toMem := Mem.mk capa
  toConfig := config
  inputs := inputs
  outputs := #[]

#check
  let state : State := mk []
  state.dbg

variable (self : State)

/-! Notice how we can use `Config`'s fields as `State` fields. -/

def withConfig (config : Config) : State :=
  {self with toConfig := config}
def withDbg (dbg : Bool) : State :=
  {self with dbg}
def withCheck (check : Bool) : State :=
  {self with check}
def withLoopLimit (loopLimit : Nat) : State :=
  {self with loopLimit}
def withNoLoopLimit : State :=
  {self with loopLimit := none}

/-! Here are a few functions to write so that you don't fall asleep. -/

/-- Apply f on mem -/
def liftMemFun (f: Mem → Mem) : State → State :=
  fun s => { s with toMem := f s.toMem }

/-- info: Zen.Train.Bf.Rt.State.liftMemFun (f : Mem → Mem) : State → State -/
#guard_msgs in #check liftMemFun

/-- Add n as output -/
def emit (n : Nat) : State  :=
  { self with outputs := #[ n ] }

/-- info: Zen.Train.Bf.Rt.State.emit (self : State) (n : Nat) : State -/
#guard_msgs in #check emit

/-- Drain first input -/
def drainInput : Nat × State :=
  match self.inputs with
  | []     => ⟨ 0, self ⟩
  | h :: t => ⟨ h, { self with inputs := t } ⟩

/-- info: Zen.Train.Bf.Rt.State.drainInput (self : State) : Nat × State -/
#guard_msgs in #check drainInput

/-- Return all outputs -/
def drainOutputs : Array Nat × State :=
  ⟨ self.outputs, { self with outputs := #[] } ⟩

/-- info: Zen.Train.Bf.Rt.State.drainOutputs (self : State) : Array Nat × State -/
#guard_msgs in #check drainOutputs



def mapCurr f := liftMemFun fun m => m.mapCurr f
def applyOp o := liftMemFun fun m => m.applyOp o
def mvl := liftMemFun .mvl
def mvr := liftMemFun .mvr
def getCurr := self.toMem.getCurr

end State



/-- Output extraction strategy.

Users will provide a value of this type to run on the outputs of their execution once it's over.
-/
inductive Extract : Type → Type 1
/-- Extracts nothing. -/
| unit : Extract Unit
/-- Extracts the array of outputs without doing anything. -/
| array : Extract (Array Nat)
/-- Yields the first output, if any. -/
| head? : Extract (Option Nat)
/-- Yields the first output, fails if none. -/
| head! : Extract Nat
/-- Folds over the outputs with a finalizer. -/
| tryFold : β → (β → Nat → Except Error β) → (β → Except Error α) → Extract α

namespace Extract

/-! Let's write more functions 🐙 -/

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.Extract.foldAnd {β α : Type} (init : β) (f : β → Nat → β) (finalCheck : β → Except Error α) : Extract α -/
#guard_msgs in #check foldAnd

-- todo 🙀
/-- info: Zen.Train.Bf.Rt.Extract.fold {α : Type} : α → (α → Nat → α) → Extract α -/
#guard_msgs in #check fold

-- todo 🙀
/-- info:
Zen.Train.Bf.Rt.Extract.apply {α : Type} (self : Extract α) : Array Nat → Except Error α
-/
#guard_msgs in #check apply


/-! Write `apply!`, which is defined as `Option.get! ∘ Except.toOption ∘ self.apply`. -/
-- todo 🙀



/-- Extracts the sum of all the outputs. -/
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



/-- String list extraction, where non-char values are interpreted as separators. -/
def strings : Extract (Array String) :=
  fold #[] combine
where
  combine stringArray n :=
    let c := Char.ofNat n
    if c.val = 0 then
      -- v~~~~ **we need this**
      if h : stringArray.size ≠ 0 then
        if let "" := stringArray.last
        then stringArray
        else stringArray.push ""
      else
        stringArray
    else
      let (curr, stringArray) :=
        -- v~~~~ **we need this too**
        if h : stringArray.size ≠ 0
        then stringArray.pop'
        else ("", stringArray)
      curr.push c |> stringArray.push

def string : Extract String :=
  foldAnd #[] strings.combine fun
    | #[s] => return s
    | strings => do
      Error.text s!"[string extractor] expected exactly one string, got {strings.size}"
      |> Except.error

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
  let s := string.apply! chars.toArray
    println! "  `{s}`"
  let chars :=
    chars ++ [0] ++ ("next bit".data.map Char.toNat)
  println! "second result:"
  for bit in strings.apply! chars.toArray do
    println! "  `{bit}`"
  let chars :=
    chars
    ++ [20^10] ++ ("and then".data.map Char.toNat)
    ++ [20130531] ++ [52016027] ++ ("finally".data.map Char.toNat)
  println! "third result:"
  for bit in strings.apply! chars.toArray do
    println! "  `{bit}`"

end Extract
