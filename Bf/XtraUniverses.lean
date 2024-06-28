namespace Zen.Train.Universes



/-! ## Type universes

- [on FPiL](https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad/universes.html)

Usually, programming languages talk almost exclusively about runtime *things*. At runtime, only
values and functions over values exist.
-/

#eval 7
#eval "cat"
#eval (2, 'n')
#eval "cat".append "s"

/-!
At compile-time, these runtime values and functions have a type.
-/

#check 7
#check "cat"
#check (2, 'n')
#check String.append
#check "cat".append
#check "cat".append "s"
#check [2, 3, 4]

/-!
Everything has a type in lean, so all these types also have a type: `Type`.
-/

#check Nat
#check String
#check Nat × Char
#check String → String → String
#check String → String
#check List Nat

/-!
Everything still has a type in Lean, so `Type` also has a type.
-/

#check Type
#check Type 1
#check Type 2
#check Type 3
-- you get it

/-!
For logical reasons, `Type`'s type cannot be `Type`. It needs to be "bigger", or "above" in some
hierarchy of types.

(See [Girard's Paradox][girard], and/or [Russell's Paradox][russel].)

[girard]: https://en.wikipedia.org/wiki/System_U#Girard's_paradox
[russel]: https://en.wikipedia.org/wiki/Russell's_paradox

`Type u` is layer `u` of this hierarchy, and `Type` is short for `Type 0`.

Let's define a list type now.
-/

inductive Lst (α : Type) : Type -- the `: Type` can be omitted
| nil
| cons : α → Lst α → Lst α

/-- info: Zen.Train.Universes.Lst (α : Type) : Type -/
#guard_msgs in #check Lst
/-- info: Lst.cons 0 (Lst.cons 1 (Lst.cons 2 (Lst.cons 3 Lst.nil))) : Lst Nat -/
#guard_msgs in #check Lst.nil.cons 3 |>.cons 2 |>.cons 1 |>.cons 0

/-!
What if we want to make a list of `Type`s?
-/

/-- error: application type mismatch
  Lst.cons String
argument
  String
has type
  Type : Type 1
but is expected to have type
  ?m.698 : Type
-/
#guard_msgs in
  #check Lst.nil.cons String

/-- error: application type mismatch
  Lst Type
argument
  Type
has type
  Type 1 : Type 2
but is expected to have type
  Type : Type 1
---
info: Lst (sorryAx Type true) : Type
-/
#guard_msgs in
  #check Lst Type

/-!
First attempt at fixing this.
-/

/-- error:
invalid universe level in constructor 'Zen.Train.Universes.Lst'.cons', parameter has type
  α
at universe level
  2
it must be smaller than or equal to the inductive datatype universe level
  1
-/
#guard_msgs in
  inductive Lst' (α : Type 1) : Type
  | nil
  | cons : α → Lst' α → Lst' α

/-- Second attempt. -/
inductive Lst' (α : Type 1) : Type 1
| nil
| cons : α → Lst' α → Lst' α


/-! Sweet! -/

/-- info: Lst' Type : Type 1 -/
#guard_msgs in #check Lst' Type

/-- info: Lst'.cons Char (Lst'.cons Nat (Lst'.cons String Lst'.nil)) : Lst' Type -/
#guard_msgs in #check Lst'.nil.cons String |>.cons Nat |>.cons Char

/-! If we want to be more generic, we need (type-)universe polymorphism. -/

namespace v0
/-- This is how Lean displays universe polymorphism. -/
inductive Lst.{u} (α : Type u) : Type u
| nil
| cons : α → Lst α → Lst α

/-- info: Lst Type : Type 1 -/
#guard_msgs in #check Lst Type

/-- info: Lst.cons Char (Lst.cons Nat (Lst.cons String Lst.nil)) : Lst Type -/
#guard_msgs in #check Lst.nil.cons String |>.cons Nat |>.cons Char

end v0

namespace v1
/-! In more complex cases it can be useful to factor out universe parameters. -/
universe u

inductive Lst (α : Type u) : Type u
| nil
| cons : α → Lst α → Lst α

/-- info: Lst Type : Type 1 -/
#guard_msgs in #check Lst Type

/-- info: Lst.cons Char (Lst.cons Nat (Lst.cons String Lst.nil)) : Lst Type -/
#guard_msgs in #check Lst.nil.cons String |>.cons Nat |>.cons Char

end v1

namespace v2

/--
In **most** cases, we can let Lean deal with universes without declaring parameters explicitely.
-/
inductive Lst (α : Type u) : Type u -- can omit `: Type u`
| nil
| cons : α → Lst α → Lst α

/-- info: Lst Type : Type 1 -/
#guard_msgs in #check Lst Type

/-- info: Lst.cons Char (Lst.cons Nat (Lst.cons String Lst.nil)) : Lst Type -/
#guard_msgs in #check Lst.nil.cons String |>.cons Nat |>.cons Char

end v2
