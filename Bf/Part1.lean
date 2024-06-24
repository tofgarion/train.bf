import Bf.Init



/-! # Types -/
namespace Zen.Train.Bf



/-! ## Inductive types

We're writing a [brainfuck](https://en.wikipedia.org/wiki/Brainfuck) interpreter, except that the
cells store `Nat`s.

- [brainfuck commands](https://en.wikipedia.org/wiki/Brainfuck#Language_design) which we will extend
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
deriving Inhabited, Repr, BEq

#check Ast.Seff
#check Ast.Seff.dbg



/-! Write an inductive `Ast.Check` type.

It has a single variant `chk` with a `Nat` cell value and a `String` message.

(It's semantic is that if the current cell's value is not the `chk` value, then the program crashes
and the message is output as an error.)
-/

section sol!
/-- Check (safety) instructions.-/
inductive Ast.Check
/-- `chk n e`: if the current cell's value is not `n` crash with error message `e`. -/
| chk : Nat → String → Check
deriving Inhabited, Repr, BEq
end sol!



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

section sol!
instance Op.instCoeAst : Coe Op Ast where
  coe op := Ast.op op
instance Seff.instCoeAst : Coe Seff Ast where
  coe := Ast.seff
instance Check.instCoeAst : Coe Check Ast :=
  ⟨.check⟩
end sol!

#check (Op.inc : Ast)
#check (Seff.dbg "checking" : Ast)
#check (Check.chk 2 "panic" : Ast)



namespace Op
/-! Write the `ofChar?` and `toChar` functions. -/

section sol!
def ofChar? : Char → Option Op
| '>' => mvr | '<' => mvl
| '+' => inc | '-' => dec
| _ => none

def toChar : Op → Char
| mvr => '>' | mvl => '<'
| inc => '+' | dec => '-'
end sol!



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



/-! Write two instances:

- `ToString Op`, and
- `ToString (Option Op)` with `'¿'` when `none`.
-/

section sol!
/-- Pretty string representation. -/
instance instToString : ToString Op :=
  ⟨toString ∘ toChar⟩
/-- Useful for debug. -/
instance instOptionToString : ToString (Option Op) where
  toString
  | none => "¿"
  | some o => toString o
end sol!

end Op



namespace Seff
/-! Same for `Seff`, though
- there is no character associated to `Seff.dbg` (so, `toChar?`), and
- `Seff.dbg some_string` is string-ified as `"dbg!(\"{some_string}\")"`.
-/

section sol!
/-- Tries to build a `Seff`. -/
def ofChar? : Char → Option Seff
| '.' => out | ',' => inp
| _ => none

/-- Character representing a `Seff`. -/
def toChar? : Seff → Option Char
| out => '.' | inp => ','
| dbg _ => none

/-- Pretty string representation. -/
instance instToString : ToString Seff where
  toString
  | out => "." | inp => ","
  | dbg s => s!"dbg!(\"{s}\")"
/-- Useful for debug. -/
instance instOptionToString : ToString (Option Seff) where
  toString
  | none => "¿"
  | some s => toString s
end sol!

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
| seq l  =>
  "" |> l.foldl fun acc ast => acc ++ ast.toString

instance instToString : ToString Ast := ⟨Ast.toString⟩



/-! Lifting the constructors of `Op`, `Seff` and `Check` to the `Ast` namespace. -/
def mvr : Ast := Ast.Op.mvr
def mvl : Ast := Ast.Op.mvl
def inc : Ast := Ast.Op.inc
def dec : Ast := Ast.Op.dec

def chain : Ast → Ast → Ast
| .seq s1, .seq s2 => .seq <| s1 ++ s2
| .seq s1, ast2 => .seq <| s1.push ast2
| ast1, .seq s2 => .seq <| #[ast1] ++ s2
| ast1, ast2 => .seq #[ast1, ast2]

def seqN : Nat → Ast → Ast :=
  (mkArray · · |> .seq)

def moveBy : Int → Ast
| .ofNat n => Ast.mvr.seqN n
| .negSucc n => Ast.mvl.seqN n.succ

example : moveBy 3 = seq #[mvr, mvr, mvr] := rfl
example : moveBy (- 2) = seq #[mvl, mvl] := rfl

def add (n : Nat) : Ast :=
  Ast.seq (Array.mkArray n .inc)
def sub (n : Nat) : Ast :=
  Ast.seq (Array.mkArray n .dec)

example : add 2 = seq #[inc, inc] := rfl
example : sub 3 = seq #[dec, dec, dec] := rfl

def out : Ast := Ast.Seff.out
def inp : Ast := Ast.Seff.inp
def dbg : String → Ast := Coe.coe ∘ Ast.Seff.dbg

def chk : Nat → String → Ast := (Ast.Check.chk · ·)

def Test.val1 : Ast := Ast.seq #[
  .inc,
  .block <| .seq #[.dec, .mvr, .inc, .inc, .mvl],
  .mvr,
  .out,
  .chk 2 "not 2 😿",
  .dbg "done"
]

/-- info: "+[->++<]>.[2?][dbg]" -/
#guard_msgs in #eval
  Test.val1.toString



/-! Write `append` which chains two `Ast`-s, and an `Append` instance. -/
#check Append

section sol!
/-- Chains two `Ast`-s. -/
def append : Ast → Ast → Ast
| seq s₁, seq s₂ => s₁ ++ s₂ |> seq
| seq s₁, rgt => s₁.push rgt |> seq
| lft, seq s₂ => #[lft] ++ s₂ |> seq
| lft, rgt => seq #[lft, rgt]

instance instAppend : Append Ast := ⟨append⟩
end sol!

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
