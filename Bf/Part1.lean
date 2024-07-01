import Bf.Init



/-! # Types -/
namespace Zen.Train.Bf



/-! ## Inductive types

We're writing a [brainfuck](https://en.wikipedia.org/wiki/Brainfuck) interpreter. Our version of
brainfuck has `Nat`-valued cells, inputs and outputs.

- [brainfuck commands](https://en.wikipedia.org/wiki/Brainfuck#Language_design)

  (We will slightly extend these commands.)
-/



/-- Brainfuck basic memory-manipulating operators. -/
inductive Ast.Op
/-- Move right: `>`. -/
| mvr : Op
/-- Move left: `<`. -/
| mvl : Op
/-- Add `1` to the current memory cell. -/
| inc : Op
/-- Sub `1` to the current memory cell. -/
| dec : Op
deriving Inhabited, Repr, BEq

#check Ast.Op
#check Ast.Op.mvr
#check Ast.Op.mvl
#check Ast.Op.inc
#check Ast.Op.dec



#check String
#check Nat



/-- Side-effect instructions. -/
inductive Ast.Seff
/-- Outputs the value of the current cell. -/
| out
/-- Reads a `Nat` and writes it to the current cell. -/
| inp
/-- Debug `println`-like instruction, **not** part of brainfuck proper. -/
| dbg : String → Seff
/-- Dumps the state. -/
| dump
deriving Inhabited, Repr, BEq

#check Ast.Seff
#check Ast.Seff.dbg



/-! Write an inductive `Ast.Check` type.

It has a single variant `chk` with a `Nat` cell value and a `String` message.

(It's semantic is that if the current cell's value is not the `chk` value, then the program crashes
and the message is output as an error.)
-/

-- todo 🙀



/-- The brainfuck AST. -/
inductive Ast
| op : Ast.Op → Ast
| seff : Ast.Seff → Ast
| check : Ast.Check → Ast
/-- A block appears as `[]` delimiters around some code. -/
| block : Ast → Ast
/-- A sequence of AST elements. -/
| seq : Array Ast → Ast

namespace Ast
/-! Write three instances:
- `Op.instCoeAst : Coe Op Ast`
- `Seff.instCoeAst : Coe Seff Ast`
- `Check.instCoeAst : Coe Check Ast`
-/

#check Coe

-- todo 🙀

#check (Op.inc : Ast)
#check (Seff.dbg "checking" : Ast)
#check (Check.chk 2 "panic" : Ast)



namespace Op
/-! Write the `ofChar?` and `toChar` functions. -/

-- todo 🙀



section proofs

theorem toChar_mvr : mvr.toChar = '>' := rfl
theorem toChar_mvl : mvl.toChar = '<' := rfl
theorem toChar_inc : inc.toChar = '+' := rfl
theorem toChar_dec : dec.toChar = '-' := rfl

theorem ofChar_toChar :
  ∀ (o : Op), ofChar? (toChar o) = some o
:= fun o => by
  cases o <;> rfl

theorem toChar_ofChar :
  ∀ (c : Char) (o : Op), ofChar? c = some o → toChar o = c
:= fun c o => by
  simp [ofChar?]
  split
  <;> simp
  <;> (intro h ; rw [← h] ; rfl)

end proofs



/-! Write two instances:

- `ToString Op`, and
- `ToString (Option Op)` with `'¿'` when `none`.
-/

-- todo 🙀

protected def toString (self : Op) := toString self

end Op



namespace Seff
/-! Same for `Seff`, though
- there is no character associated to `Seff.dbg` (so, `toChar?`), and
- `Seff.dbg some_string` is string-ified as `"dbg!(\"{some_string}\")"`.
-/

-- todo 🙀

protected def toString (self : Seff) := toString self

section proofs

theorem toChar_out : out.toChar? = '.' := rfl
theorem toChar_inp : inp.toChar? = ',' := rfl
theorem toChar_dbg : (dbg "msg").toChar? = none := rfl

end proofs

end Seff



namespace Check
/-! This one's on me. -/

/-- Pretty string representation. -/
protected def toString : Check → String
| chk val blah => s!"chk!({val}, \"{blah}\")"

instance instToString : ToString Check := ⟨Check.toString⟩
end Check



protected partial
def toString : Ast → String
| op o =>
  toString o
| seff (.dbg _) =>
  "[dbg]"
| seff s =>
  toString s
| check (.chk exp _msg) =>
  s!"[{exp}?]"
| block b =>
  s!"[{b.toString}]"
| seq a =>
  "" |> a.foldl fun acc ast => acc ++ ast.toString

instance instToString : ToString Ast := ⟨Ast.toString⟩



/-! Lifting the constructors of `Op`, `Seff` and `Check` to the `Ast` namespace. -/

def mvr : Ast := Op.mvr
def mvl : Ast := Op.mvl
def inc : Ast := Op.inc
def dec : Ast := Op.dec

def out : Ast := Seff.out
def inp : Ast := Seff.inp
def dbg : String → Ast := Coe.coe ∘ Seff.dbg
def dump : Ast := Seff.dump

def chk : Nat → String → Ast := (Check.chk · ·)



/-! A few helpers. -/

def blockSeq : Array Ast → Ast :=
  (block <| seq ·)

def seqN : Nat → Ast → Ast :=
  (seq <| mkArray · ·)



/-! Write `moveBy` which takes an `i : Int` and moves right (left) `i` cells if `0≤i` (`i<0`). -/

#check Int

-- todo 🙀

example : moveBy 3 = seq #[mvr, mvr, mvr] := rfl
example : moveBy 0 = seq #[] := rfl
example : moveBy (- 2) = seq #[mvl, mvl] := rfl



def add (n : Nat) : Ast :=
  seq (Array.mkArray n .inc)
def sub (n : Nat) : Ast :=
  seq (Array.mkArray n .dec)

example : add 2 = seq #[inc, inc] := rfl
example : sub 3 = seq #[dec, dec, dec] := rfl

/-- `+[->++<]>.[2?][dbg("done")]` -/
def Test.val1 : Ast := seq #[
  inc,
  block <| seq #[dec, mvr, inc, inc, mvl],
  mvr,
  out,
  chk 2 "not 2 😿",
  dbg "done"
]

/-- info: "+[->++<]>.[2?][dbg]" -/
#guard_msgs in #eval
  Test.val1.toString



/-! Write `chain` which chains two `Ast`-s, see `#eval` below. -/

-- todo 🙀

/-- info: +- +- +- +- -/
#guard_msgs in #eval do
  println! "{chain inc dec}"
  println! "{chain (seq #[inc]) dec}"
  println! "{chain inc (seq #[dec])}"
  println! "{chain (seq #[inc]) (seq #[dec])}"



/-! Write an `Append` instance. -/
#check Append

-- todo 🙀

/-- info:
+[->++<]>.[2?][dbg]+
++[->++<]>.[2?][dbg]
++
+[->++<]>.[2?][dbg]+[->++<]>.[2?][dbg]
-/
#guard_msgs in #eval do
  println! Test.val1 ++ Ast.inc
  println! Ast.inc ++ Test.val1
  println! Ast.inc ++ Ast.inc
  println! Test.val1 ++ Test.val1
