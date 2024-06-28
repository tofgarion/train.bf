import Bf.Xtra1Universes


namespace Zen.Train.Xtra.Propositional



/-! What if we wanted to encode some logic?

The Curry-Howard isomorphism point of view is

- propositions (theorems) are types
- proofs are programs

A proposition `P` is proved by *constructing* a value `p : P`.

For instance, proving an *implication* `P → Q` means "given a proof for `P`, produce a proof for
`Q`". So it's just a *function* that takes a `P`-value (proof) and produces a `Q`-value (proof).

Note that we actually do not care about the value/proof of a proposition, just that one exists. We
only care that the type is inhabited.

Note that (in general) we actually do not care about the value/proof of a proposition, just that one
exists. We only care that the type is inhabited. So as long as we can write a function with
signature `P → Q`, then we know `P → Q` and the **well-typed** definition of the function does not
matter.
-/
namespace TypeOnly



/-- No work needed to prove (construct) `True`. -/
inductive Tru
| intro
deriving Inhabited -- don't mind that

/-- Impossible to prove (construct) `False`. -/
inductive Fls


/-! Note that it is *crucial* that we are in a pure, **total**, **terminating** language.

Otherwise we could write functions that prove anything, including false.
-/

def badButOkay : Tru :=
  panic! "I'm just lazy"

/-- error: failed to synthesize instance
  Inhabited Fls
-/
#guard_msgs in
def illogicPanic : Fls :=
  panic! "just trust me"

/-- error:
fail to show termination for
  Zen.Train.Xtra.Propositional.TypeOnly.illogicRec
with errors
structural recursion cannot be used

well-founded recursion cannot be used, 'Zen.Train.Xtra.Propositional.TypeOnly.illogicRec' does not take any (non-fixed) arguments
-/
#guard_msgs in
def illogicRec : Fls :=
  illogicRec



/-! What about negation, conjuction and disjunction? -/

structure Conj (P₁ P₂ : Type) where
intro ::
  lft : P₁
  rgt : P₂

inductive Disj (P₁ P₂ : Type)
| inLft : P₁ → Disj P₁ P₂
| inRgt : P₂ → Disj P₁ P₂

def disj_of_conj : Conj P Q → Disj P Q
| ⟨lft, _⟩ => .inLft lft



/-! What about negation? -/

abbrev Not (P : Type) :=
  P → Fls

def not_disj_of_not_not : Not P → Not Q → Not (Disj P Q)
| n_p, _, .inLft p => n_p p
| _, n_q, .inRgt q => n_q q

def not_conj_of_not_disj : Not (Disj P Q) → Not (Conj P Q)
| n_p_or_q, ⟨p, _⟩ => n_p_or_q <| Disj.inLft p

def not_conj_of_not_not : Not P → Not Q → Not (Conj P Q) :=
  (not_conj_of_not_disj <| not_disj_of_not_not · ·)

def contra : (P → Q) → Not Q → Not P
| q_of_p, nq, p => q_of_p p |> nq



/-! Equivalence? -/

inductive Eq : Type → Type → Type :=
| refl : Eq P P



/-! We can't go much further than that using only `Type`.

Given `Eq`'s signature for instance, we can't express that two `Nat`urals are equivalent.
-/

/-- error: application type mismatch
  Eq n
argument
  n
has type
  Nat : Type
but is expected to have type
  Type : Type 1
-/
#guard_msgs(error, drop info) in
#check (n m : Nat) → Eq n m

end TypeOnly



/-! What we'd like is a special world to talk about propositions, for several reasons.

- We want some logical constructions to range over more than propositions (`Type`), typically
  values, such as `Eq n m` where `n m : Nat`.

- `Type` is the really the world of the runtime, *programs* (functions) in `Type` are computations
  that will be compiled.

  Propositional *programs* (functions) are just proofs and *in general* only their signature is
  relevant.

- More generally, the propositional world works very differently from the computational one in
  practice. So we want (*need*, really) to distinguish them, for instance to create data structures
  that work only in the computational world.

This propositional world is called `Prop`.
-/

/-- info: True : Prop -/
#guard_msgs in #check True
/-- info: False : Prop -/
#guard_msgs in #check False

/-- info: And : Prop → Prop → Prop -/
#guard_msgs in #check @And
/-- info: Or : Prop → Prop → Prop -/
#guard_msgs in #check @Or

/-- info: Not : Prop → Prop -/
#guard_msgs in #check @Not

/-- info: Eq.{u_1} {α : Sort u_1} : α → α → Prop -/
#guard_msgs in #check Eq

/-! Alright, what's `Sort`?

`Sort` is the notion below `Type`, in the sense that `Type _` is really sugar for a `Sort _`.

Similar to `Type ≝ Type 0`.

| sugar  |     `Sort`     |  `Type`  |
| :----: | :------------: | :------: |
| `Prop` |    `Sort 0`    |          |
| `Type` |    `Sort 1`    | `Type 0` |
|        |    `Sort 2`    | `Type 1` |
|        |      ...       |   ...    |
|        | `Sort (u + 1)` | `Type u` |

So `Eq`'s signature tells us that `α` can be any type we want, including a `Prop`osition (`Sort 0`)
or a `Type` (`Type 0`, `Sort 1`).

Note also that the actual parameters of `Eq` are `α`-**values**.
-/

-- notice how this signature is different from usual (`Type u`) function signatures
/-- info: ∀ (n m : Nat), n = m : Prop -/
#guard_msgs in #check (n m : Nat) → Eq n m
/-- info: Nat = String : Prop -/
#guard_msgs in #check Eq Nat String

/-!
For (counter)example, `List` works on anything but `Prop` as its parameter is `Type u`.
-/

/-- info: List.{u} (α : Type u) : Type u -/
#guard_msgs in #check List



/-! (Most of) you are not `Prop` proof experts with just that. It takes huge amounts of effort and time.

Here are a few things to look at.
-/

/-- Membership in a list as a proposition. -/
inductive ListMem : α → List α → Prop
| head : (hd : α) → (tl : List α) → ListMem hd (hd::tl)
| cons : {hd : α} → {tl : List α} → (a : α) → ListMem hd tl → ListMem hd (a::tl)

-- a `theorem` is a `Prop`ositional `def` that can't be unfolded
theorem mem_tail_of_mem_not_head'
  {a hd : α} {tl : List α}
: a ≠ hd → ListMem a (hd :: tl) → ListMem a tl
-- -- Lean is smart enough to see that this doesn't make sense
-- | a_ne_hd, ListMem.head _ _ =>
--   False.elim (a_ne_hd rfl)
| _, ListMem.cons _ a_in_tl =>
  a_in_tl

/-! That was terrible, that's neither how propositions or proofs are written. -/

theorem mem_tail_of_mem_not_head
: ∀ {a hd : α} {tl : List α}, a ≠ hd → ListMem a (hd :: tl) → ListMem a tl :=
  by
    -- tactic mode!
    intro a hd tl a_ne_hd a_in_cons
    cases a_in_cons
    · contradiction
    · assumption



/-! Further reading. -/
#check Decidable
#check Decidable.em
#check Decidable.predToBool



/-! One last thing.

**NB**: `Prop` is **not** `Bool`.
- `Bool : Type` is made of values to be computed at runtime;
- `Prop` is a type universe, its members are propositions that may be provable using Lean's
  underlying type theory (CIC / dependent type theory).
  In particular `Prop` **can** represent non-decidable propositions and non-computable quantities
  such as (mathematical) [sets], [reals], *etc.*

[sets]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html#Set
[reals]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html#Real
-/

abbrev Set (α : Type u) := α → Prop

namespace Set
variable (self : Set α)

abbrev mem (a : α) : Prop := self a

abbrev insert (a : α) : Set α :=
  fun e => e = a ∨ self.mem e

abbrev remove (a : α) : Set α :=
  fun e => e ≠ a ∧ self.mem e

abbrev union (that : Set α) : Set α :=
  fun e => self.mem e ∨ that.mem e

abbrev inter (that : Set α) : Set α :=
  fun e => self.mem e ∧ that.mem e

-- `example` is a nameless `theorem`
example : ∀ {s1 s2 : Set α} {a : α}, (s1.inter s2).mem a → (s1.union s2).mem a := by
  intro s1 s2 a
  simp [inter, union, mem]
  intro _
  exact Or.inr
end Set


/-! This last example looks terrible because no notation boilerplate is in place.

Here are a few theromes with the actual [`Set`] type (mathlib needed):

- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set.not_mem_diff_of_mem>
-/
