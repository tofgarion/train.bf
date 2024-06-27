import Bf.Init



/-! # Monads and `do` notation -/
namespace Zen.Train.Trash.MonadsAndDo



/-! A monad wraps values of any type `α` and is equipped with two operations. -/

/-- For instance: -/
abbrev Just : Type → Type := id

#check Just

namespace Just
def get : Just α → α := id

/-- Injects a value into the monad. -/
protected def pure (val : α) : Just α :=
  val

/-- Given a `Just α`-value, apply a function to the inner `α` that returns a `Just β`-value. -/
protected def bind (justVal : Just α) (f : α → Just β) : Just β :=
  f justVal


/-! Now check this out.

```
let mut val := 7
if 0 < val then
  val := val - 1
val := val % 2
```

This is obviously not compatible with a pure language. Or is it?
-/

def encodeLetMut (val : Nat) : Just Nat :=
  Just.pure val
  |>.bind (fun val =>
    let val := if 0 < val then val - 1 else val
    Just.pure val
  )
  |>.bind (fun val =>
    Just.pure (val % 2)
  )

example : encodeLetMut 7 = Just.pure 0 := rfl
example : encodeLetMut 0 = Just.pure 0 := rfl
example : encodeLetMut 8 = Just.pure 1 := rfl



/-! This is basically how the `do` notation works for `Monad`s. -/

#checkout Monad

instance instMonad : Monad Just where
  pure := Just.pure
  bind := Just.bind

def doLetMut (val : Nat) : Just Nat := do
  let mut val := val
  if 0 < val then val := val - 1
  return val % 2 -- same as `pure (val % 2)`

end Just



/-! ## `do` notation: `←`

Define an option type `Opt : Type → Type` with variants `non`e and `som`e.

(To avoid clashing with Lean's `Option` type).
-/

section sol!
inductive Opt (α : Type) : Type
| non
| som : α → Opt α
end sol!

#check Opt.non
#check Opt.som

namespace Opt

/-! Write a `ToString` instance for `Opt`. -/
section sol!
instance instToString [ToString α] : ToString (Opt α) where
  toString
    | non => "none"
    | som a => toString a
end sol!

/-! Write a `Monad` instance for `Opt`. -/
section sol!
instance instMonad : Monad Opt where
  pure := som
  bind
  | non, _ => non
  | som a, f => f a
end sol!



/-! We can use `←` to "access the value", *i.e.* trigger a bind. -/

def map (a? : Opt α) (f : α → β) : Opt β := do
  let a ← a? -- using `←` instead of `:=`
  return f a -- again, `return <term>` is just `pure (<term>)`

def map' (a? : Opt α) (f : α → β) : Opt β := do
  -- you can also do this
  return f (← a?)

def mapWithBind (a? : Opt α) (f : α → β) : Opt β :=
  -- `bind a? (pure ∘ f)`, but let's write it with the infix `>>=` bind operator to look cool
  a? >>= pure ∘ f


def demo (a? : Opt Nat) : Opt Nat := do
  if let 0 ← a?
  then non else
    match ← a? with
    | 0 => panic! "unreachable!"
    | 7 => return 7
    | _ => non

/-! `#eval` actually takes a term of type `IO α`, and `IO` is a monad. -/
#checkout IO
#checkout IO.println

#eval do
  let mut val := demo (som 0)
  -- same as `IO.println` but takes an interpolated string
  println! "{val}"
  -- has type `IO Unit`, `do` notation lets us chain `M Unit` expressions when `M` is a monad

  val := demo (som 1) -- also has type `M Unit` (`IO Unit`, here)
  println! "{val}"
  val := demo (som 7)
  println! "{val}"
  return ()

end Opt



/-! ## State monads

Exercise / discussion

In a purely functional language, how would you write a function that produces some result `α` but
also

- just reads some state?
- reads and write some state?
-/

structure State where
  counter : Nat

section sol!
def justReads (params : Nat) (state : State) : Nat :=
  params + state.counter

-- alternatively
def justReads' (params : Nat) : State → Nat :=
  fun state => params + state.counter

def readsWrites (params : Nat) (state : State) : Nat × State :=
  let out := justReads params state
  let state := { state with counter := state.counter + 1 }
  (out, state)

-- alternatively
def readsWrites' (params : Nat) : State → Nat × State :=
  fun state =>
    let out := justReads params state
    let state := { state with counter := state.counter + 1 }
    (out, state)
end sol!



/-! What would be the corresponding monads `ReadM` and `WriteM` for some generic state type `σ`? -/

section sol!
abbrev ReadM (σ : Type) (α : Type) : Type :=
  σ → α

abbrev WriteM (σ : Type) (α : Type) : Type :=
  σ → α × σ
  -- same as `ReadM σ (α × σ)`
end sol!



/-! Now just write `Monad` instances for them. -/

section sol!
instance ReadM.instMonad : Monad (ReadM σ) where
  pure a _state := a
  bind a? f? state :=
    let a := a? state
    f? a state

instance WriteM.instMonad : Monad (WriteM σ) where
  pure := Prod.mk
  bind a? f? state :=
    let (a, state) := a? state
    f? a state
end sol!



/-! Awesome, now we can define a few helpers. -/

def ReadM.get : ReadM σ σ
| state => state

def WriteM.get : WriteM σ σ
| state => (state, state)

def WriteM.set : σ → WriteM σ Unit
| newState, _oldState => ((), newState)



abbrev Log := Array String

def WriteM.demo (n : Nat) : WriteM Log Nat := do
  log "checking if `n` is zero"
  if n = 0 then
    log' "`n` is zero!"
    return n
  else
    log "`n` is not zero, modulo-2-ing it"
    return n % 2
where
  log (msg : String) : WriteM Log Unit := do
    let log ← get
    set <| log.push msg
  /-- Arguably simpler, arguably not as fancy. -/
  log' (msg : String) : WriteM Log Unit
    | log => ((), log.push msg)


/-! Write `WriteM.runDemo : IO Unit` that runs `WriteM.demo` on some inputs, shows the results and
log for each call.
-/

section sol!
def WriteM.runDemo : IO Unit := do
  let state := #[]
  let (res, state) := demo 7 state
  println! "demo 7"
  -- so, turns out we can also `for`-iterate on collections when in a monad 😺
  -- see the `ForIn` class for details
  for line in state do
    println! "- {line}"
  println! "↦ {res}"
  println! ""

  let state := #[]
  let (res, state) := demo 0 state
  println! "demo 7"
  for line in state do
    println! "- {line}"
  println! "↦ {res}"
  println! ""

  let state := #[]
  let (res, state) := demo 10 state
  println! "demo 7"
  for line in state do
    println! "- {line}"
  println! "↦ {res}"
end sol!

#eval WriteM.runDemo

end MonadsAndDo



/-! The `Just` monad is called `Id` in Lean. -/
#checkout Id
#checkout (inferInstance : Monad Id) -- would fail if no `Monad Id` instances existed



/-! The cool thing is that we can run imperative-looking code whenever we want with `Id`. -/
#checkout Id.run

/-- Array pretty-printer (`pp`). -/
private
def ppArray [ToString α]
  (array : Array α)
  (sep : String := ", ")
  (delim : String × String := ("#[", "]"))
: String := Id.run do
  let mut s := ""
  for elm in array do
    if ¬ s.isEmpty then
      s := s ++ sep
    s := s ++ toString elm
  delim.1 ++ s ++ delim.2

/-- info:
#[1, 2, 3]
#[1 - 2 - 3]
<| 1 | 2 | 3 |>
<| 1 | 2 | 3 |>
⟦1 · 2 · 3⟧
-/
#guard_msgs in #eval do
  let array := #[1, 2, 3]
  println! "{ppArray array}"
  let s := ppArray array " - "
  println! "{s}"
  let s := ppArray array " | " ("<| ", " |>")
  println! "{s}"
  let s := ppArray array " | " ("<| ", " |>")
  println! "{s}"
  let s := ppArray (delim := ("⟦", "⟧")) (sep := " · ") array
  println! "{s}"



/-! ## Monad transformers

Now, what if we want a state monad that allows operations from other monads such as `IO`, or the
*result* monad `Except ε`?
-/

abbrev BadSMonT (σ : Type) (M : Type → Type) (α : Type) : Type :=
  M (σ → α × σ)

abbrev SMonT (σ : Type) (M : Type → Type) (α : Type) : Type :=
  σ → M (α × σ)

namespace SMonT
instance instMonad [Monad M] : Monad (SMonT σ M) where
  pure a state := pure (a, state)
  bind a? f? state := do
    let (a, state) ← a? state
    f? a state

variable [Monad M]

/-! Write the following functions. -/
section sol!
def get : SMonT σ M σ
| state => return (state, state)

def set (state : σ) : SMonT σ M Unit
| _oldState => return ((), state)

def printState [ToString σ] : SMonT σ IO Unit
| state => do
  println! "state: {state}"
  return ((), state)
end sol!

/-- info: Zen.Train.Trash.SMonT.get {M : Type → Type} [Monad M] {σ : Type} : SMonT σ M σ -/
#guard_msgs in #check get
/-- info:
Zen.Train.Trash.SMonT.set {M : Type → Type} [Monad M] {σ : Type} (state : σ) : SMonT σ M Unit
-/
#guard_msgs in #check set
/-- info: Zen.Train.Trash.SMonT.printState {σ : Type} [ToString σ] : SMonT σ IO Unit -/
#guard_msgs in #check printState

/-- info:
state: 7
final state is `7`
-/
#guard_msgs in #eval do
  let state := 7
  let (_, state) ← printState state
  println! "final state is `{state}`"



/-! It's tedious to have to "deconstruct" our monad transformer to run `M`-code.

Check out this class, and write the appropriate instance.
-/
#checkout MonadLift

section sol!
instance instMonadLift : MonadLift M (SMonT σ M) where
  monadLift a? state := do
    let a ← a?
    return (a, state)
end sol!

/-! This gives access to `liftM` which (here) can lift `IO`-code to `SMonT σ IO`-code. -/

def printState' [ToString σ] : SMonT σ IO Unit := do
  let state ← get
  liftM $ println! "state: {state}"

/-- info:
state: 7
final state is `7`
-/
#guard_msgs in #eval do
  let state := 7
  let (_, state) ← printState' state
  println! "final state is `{state}`"



/-! What if `M` is not really `IO`, but just something that `MonadLift`-s from `IO`? -/
def printState'' [MonadLift IO M] [ToString σ] : SMonT σ M Unit := do
  let state ← get
  liftM $ println! "state: {state}"

/-! This is too easy, now we can write functions like these. Right? -/

/-- error:
failed to synthesize instance
  MonadLift IO IO
-/
#guard_msgs in
def printState''IO [ToString σ] : SMonT σ IO Unit :=
  printState''

/-! We can't 🙀

Let's actually check `liftM`'s type:
-/
#checkout liftM
/-! which leads us to: -/
#checkout MonadLiftT

/-! Let's try this again. -/
def printState''' [MonadLiftT IO M] [ToString σ] : SMonT σ M Unit := do
  let state ← get
  liftM $ println! "state: {state}"

def printState'''IO [ToString σ] : SMonT σ IO Unit :=
  printState'''

/-! Nice. -/

end SMonT
