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

def toString : Error → String
| text msg => s!"{msg}"
| loopLimit limit count _ => s!"\
  potential infinite loop detected \
  after {count} non-decreasing iterations \
  (limit is {limit})\
"
| checkFailed msg exp val _ =>
  s!"value check failed, expected `{exp}`, got `{val}`: {msg}"

instance instToString : ToString Error :=
  ⟨toString⟩

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


section sol!
structure Mem where
private mkRaw ::
  mem : Array Nat
  ptr : Fin mem.size
end sol!

namespace Mem

/-!
**NB**: remember that autocompletion is your friend, and so is Lean's documentation:

- <https://leanprover-community.github.io/mathlib4_docs>


Write the following functions, their semantics should be straightforward from their signatures.
-/

/-!
**NB**: when you need to prove something simple, try `by simp` in case it works.
-/
section sol!
def mk (capacity : Nat := 123) : Mem where
  mem := Array.mkEmpty capacity |>.push 0
  ptr := ⟨0, by simp⟩
end sol!
/-- info: Zen.Train.Bf.Rt.Mem.mk (capacity : Nat := 123) : Mem -/
#guard_msgs in #check mk



variable (self : Mem)

def mapCurr (f : Nat → Nat) : Mem :=
  let val := f self.mem[self.ptr]
  let mem := self.mem.set self.ptr val
  let tmp : mem.size = self.mem.size :=
    by simp [mem]
  ⟨mem, tmp ▸ self.ptr⟩



section sol!
def getCurr : Nat :=
  self.mem[self.ptr]
end sol!
/-- info: Zen.Train.Bf.Rt.Mem.getCurr (self : Mem) : Nat -/
#guard_msgs in #check getCurr



/-! Note: `Ast.mvl` does nothing if we're pointing to the first cell of the array. (Maybe look at
what `Nat` subtraction does.)

Also, for no reason at all, maybe take a look at these.
-/
#checkout Nat.lt_of_le_of_lt
#checkout Nat.pred_le
section sol!
def mvl : Mem := {self with
  ptr := ⟨
    self.ptr - 1,
    Nat.lt_of_le_of_lt self.ptr.val.pred_le self.ptr.isLt,
  ⟩
}
end sol!
/-- info: Zen.Train.Bf.Rt.Mem.mvl (self : Mem) : Mem -/
#guard_msgs in #check mvl



/-! This next one is more advanced, take a look but we go over it together.

We will use the following two theorems though, you can check them out.
-/
#checkout Array.size_push
#checkout Nat.succ_lt_succ
section sol!
def mvr : Mem :=
  if isLt : self.ptr.val + 1 < self.mem.size
  then { self with ptr := ⟨self.ptr.val + 1, isLt⟩ }
  else
    let mem := self.mem.push 0
    { self with
        mem
        ptr := ⟨self.ptr.val + 1, by simp [mem, Array.size_push, Nat.succ_lt_succ]⟩
    }
end sol!
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
protected def default : Config where
  dbg := true
  check := true
  loopLimit := some 123

instance instInhabited : Inhabited Config where
  default := Config.default
end Config



/-- The full state, extends `Mem` with some configuration and the inputs/outputs. -/
structure State extends Mem, Config where
private mkRaw ::
  inputs : List Nat
  outputs : Array Nat

namespace State

def mk (inputs : List Nat) (capa : Nat := 123) (config : Config := default) : State where
  toMem := Mem.mk capa
  toConfig := config
  inputs := inputs
  outputs := #[]

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

/-! Here are a few functions to write so that you don't fall asleed. -/
section sol!
private def liftMemFun (f : Mem → Mem) : State → State
| self => {self with toMem := f self.toMem}

def emit (n : Nat) : State :=
  {self with outputs := self.outputs.push n}

def drainInput : Nat × State :=
  match self.inputs with
  | [] => (0, self)
  | nxt::inputs => (nxt, {self with inputs})

def drainOutputs : Array Nat × State :=
  (self.outputs, {self with outputs := #[]})
end sol!

/-- info: Zen.Train.Bf.Rt.State.liftMemFun (f : Mem → Mem) : State → State -/
#guard_msgs in #check liftMemFun
/-- info: Zen.Train.Bf.Rt.State.emit (self : State) (n : Nat) : State -/
#guard_msgs in #check emit
/-- info: Zen.Train.Bf.Rt.State.drainInput (self : State) : Nat × State -/
#guard_msgs in #check drainInput
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
/-- Folds over the outputs, allowed to fail. -/
| tryFold : α → (α → Nat → Except Error α) → Extract α

namespace Extract

abbrev Out : Extract α → Type := 𝕂 α

/-! Let's write more functions 🐙 -/

section sol!
def fold (init : α) (f : α → Nat → α) : Extract α :=
  tryFold init (f · · |> .ok)
end sol!
/-- info: Zen.Train.Bf.Rt.Extract.fold {α : Type} (init : α) (f : α → Nat → α) : Extract α -/
#guard_msgs in #check fold

section sol!
/- I know, you haven't seen monads yet, we'll see this version after the interlude. -/
def apply : (self : Extract α) → Array Nat → Except Error α
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

def apply' : Extract α → Array Nat → Except Error α
| unit, _ => .ok ()
| array, a => .ok a
| head?, a =>
  if h : 0 < a.size then .ok a[0] else .ok none
| head!, a => do
  if h : 0 < a.size then .ok a[0] else
    .error <| .text "[bf] failed to extract output `head!`, no output available"
| tryFold init f, l =>
  applyTryFold init f l.data
where
  applyTryFold {α : Type} init f : List Nat → Except Error α
  | [] => .ok init
  | hd::tl =>
    match f init hd with
    | .ok init => applyTryFold init f tl
    | .error e => .error e
end sol!
/-- info:
Zen.Train.Bf.Rt.Extract.apply {α : Type} (self : Extract α) : Array Nat → Except Error α
-/
#guard_msgs in #check apply


/-! Write `apply!`, which is defined as `Option.get! ∘ Except.toOption ∘ self.apply`. -/
section sol!
def apply! [Inhabited α] (self : Extract α) :=
  Option.get! ∘ Except.toOption ∘ self.apply
end sol!



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
def string : Extract (Array String) :=
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
    ++ [20^10] ++ ("and then".data.map Char.toNat)
    ++ [20130531] ++ [52016027] ++ ("finally".data.map Char.toNat)
  println! "third result:"
  for bit in string.apply! chars.toArray do
    println! "  `{bit}`"

end Extract
