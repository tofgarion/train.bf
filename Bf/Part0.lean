/-! # So you want to Lean 4 -/
namespace Zen.Train.Bf.Trash



/-! ## `#check`, inductive types, and structures

- gives you the *type* of a *term* in the "infoview"
- right-click on types and "go to definition" to see how they're defined
-/

#check true
#check false
#check Bool

#check 0
#check 17
#check Nat

#check "cat"
#check String

#check (17, "cats")
#check Nat × String
#check Prod

#check ['c', 'a', 't']
#check List
#check List Char

#check some "cat"
#check Option
#check Option String



/-! ## `#eval` and expressions

- evaluates a term and shows a `Repr`esentation of the result in the infoview
- only works for simple types (with a `Repr` instance)
-/

#eval 1
#eval 1 + 2

#eval "my " ++ "cat"



/-! ### `if`-`then`-`else` -/

#eval if "cat" = "mine" then 1 else 2



/-! ### `let`-bindings -/

#eval
  let catNoise := "にゃ";
  let silent : Bool := true; -- explicit type annotation, not needed here
  if silent then (
    let pair := ("cat", "nothing");
    let middle := " says ";
    let (pref, suff) := pair; -- destructuring `let`-binding
    s!"{pref}{middle}{suff}"
  ) else (
    let result := s!"cat says `{catNoise}`";
    result
  )

/-! Same with `silent := false` and no delimiters. -/

#eval
  let catNoise := "にゃ"
  let silent : Bool := false
  if silent then
    let pair := ("cat", "nothing")
    let middle := " says "
    let (pref, suff) := pair
    s!"{pref}{middle}{suff}"
  else
    let result := s!"cat says `{catNoise}`"
    result

/-! Defining functions with `let`-bindings, and calling them. -/

#eval
  let (catNoise, silent) := ("にゃ", false)
  let app (s : String) (s' : String) : String :=
    s ++ " " ++ s'
  if silent then
    app "cat" (app "says" catNoise)
  else
    app "cat" $ app "says" "nothing"

#eval
  let work (name noise : String) (silent : Bool) : String :=
    name ++ " says " ++ if silent then "nothing" else noise
  let doit (silent : Bool) : String :=
    work "猫" "にゃ" silent
  (doit true, doit false)

/-! Same, just more fancy. -/

#eval
  let work (name noise : String) : Bool → String :=
    fun silent =>
      s!"{name} says {if silent then "nothing" else noise}"
  let doit : Bool → String :=
    work "猫" "にゃ"
  (doit true, doit false)



/-! ## Simple function definitions -/

def makeNoise? (name noise : String) (silent : Bool) : String :=
  s!"{name} says {if silent then "nothing" else noise}"

structure Cat where
  name : String
  noise : String

#check Cat
#check Cat.mk
#check Cat.name
#check Cat.noise

namespace Cat

def mine : Cat where
  name := "Edouard"
  noise := "にゃ"

def yours : Cat := {
  name := "Alba"
  noise := "meow"
}

def maigo : Cat :=
  ⟨"迷子", "mee"⟩

def makeNoise? (self : Cat) : Bool → String :=
  Trash.makeNoise? self.name self.noise

#eval mine.makeNoise? false
#eval yours.makeNoise? false
#eval maigo.makeNoise? true

end Cat



/-! ## Pattern matching -/

#check Nat

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _n => false

def isZero' : Nat → Bool
| .zero => true
| .succ _n => false

def isZero'' : Nat → Bool
| 0 => true
| _n + 1 => false



/-! ## Type parameters, (automatic) implicit arguments, and variables -/

#check Option

def getLD'' (α : Type) (a? : Option α) (getDefault : Unit → α) : α :=
  -- `if`-`let` style
  if let some a := a?
  then a
  else getDefault ()

#check getLD''
#check getLD'' String
#eval getLD'' String (some "result") (fun _ => "unreachable")
#eval getLD'' String none (fun _ => "default")
#eval getLD'' (α := String) (a? := none) (getDefault := fun _ => "default")
#eval getLD'' (getDefault := fun _ => "default") (α := String) (a? := none)

def getLD' {α : Type} (a? : Option α) (getDefault : Unit → α) : α :=
  if let some a := a? then a else getDefault ()

#check getLD'
#eval @getLD' String none fun _ => "default"
#eval getLD' none fun _ => "default"

def getLD (a? : Option α) (getDefault : Unit → α) : α :=
  if let some a := a? then a else getDefault ()

#check getLD
#eval @getLD String none fun _ => "default"
#eval getLD none fun _ => "default"



inductive Opt (α : Type)
| non | som : α → Opt α

namespace Opt

def get? : Opt α → Option α
| non => none
| som a => a

def getD : Opt α → α → α
| non, a => a
| som a, _ => a

def getLD : Opt α → (Unit → α) → α
| non, getD => getD ()
| som a, _ => a

variable {α β : Type} (self : Opt α) (f : α → β)

def map : Opt β :=
  match self with
  | non => non
  | som a => f a |> som

def mapComp (g : β → γ) : Opt γ :=
  self.map (g ∘ f)

end Opt



/-! ## Recursion and `where` -/

/-- You knew this was coming. -/
def fib : Nat → Nat
| 0 => 0
| n + 1 => loop 0 1 n
where
  loop (pre curr : Nat) : Nat → Nat
  | 0 => curr
  | n + 1 => loop curr (pre + curr) n

#eval
  -- these indices yield prime fibonacci numbers
  let block :=
    [
      2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
      53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
      101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
      151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199
    ].map (fun n => s!"fib {n} := {fib n}")
    |>.foldl (fun s line => s ++ "\n  " ++ line) ""
  println! "testing `fib`:{block}"


/-! ## Your turn

- write `L` a generic list type with a `nl` "nil" variant and a `cs` "cons" variant

  **add `deriving BEq` at the end of your type definition** (for my checks)
-/

section sol!
  inductive L (α : Type) : Type
  | nl
  | cs : α → L α → L α
  deriving BEq
end sol!

#check L
#check L.nl
#check L.cs

namespace L

def test₁ : L Nat :=
  nl.cs 3 |>.cs 2 |>.cs 1 |>.cs 0



/-! Notice that we are inside the `L` namespace now.

- write the `head?` and `tail?` functions
-/

section sol!
  def head? : L α → Option α
  | nl => none
  | cs hd _ => hd

  def tail? : L α → Option (L α)
  | nl => none
  | cs _ tl => tl
end sol!

#check L.head?
#check L.tail?

#guard (nl : L Nat).head? == none
#guard (nl : L Nat).tail? == none
#guard test₁.head? == some 0
#guard test₁.tail? == some (nl.cs 3 |>.cs 2 |>.cs 1)

/-- Just showing off. -/
theorem head?_cons : ∀ {hd : α} {tl : L α}, (tl.cs hd).head? = hd :=
  rfl



/-!
- write a `map` over `L`
-/

section sol!
def map (f : α → β) : L α → L β
| nl => nl
| cs hd tl => cs (f hd) (tl.map f)
end sol!

def test₁Mapped : L String :=
  test₁.map toString

def test₂ : L String :=
  nl.cs "3" |>.cs "2" |>.cs "1" |>.cs "0"

#guard test₁Mapped == test₂



/-!
- and now a `foldl`, "init" argument must come before the "function" argument
-/

section sol!
def foldl (init : β) (f : β → α → β) : L α → β
| nl => init
| cs hd tl =>
  let acc := f init hd
  tl.foldl acc f
end sol!

def test₁Sum : Nat :=
  test₁.foldl 0 (· + ·)

#guard test₁Sum == 6

end L



/-! ## Typeclasses -/

structure ToStrStruct (α : Type) where
  toString : α → String

#check ToStrStruct
#check ToStrStruct.toString

def ToStrStruct.apply (self : ToStrStruct α) (a : α) : String :=
  self.toString a

#check ToStrStruct.apply

class ToStr (α : Type) where
  toString : α → String

#check ToStr
#check ToStr.toString

def ToStr.apply (self : ToStr α) (a : α) : String :=
  self.toString a

#check ToStr.apply

#check ToString
#check Functor

/-! They're (almost) the same. But `class`es let us define `instance`s. -/

instance ToStr.instNat : ToStr Nat where
  toString n := s!"{n}"

#check ToStr.instNat

instance ToStr.instString : ToStr String := {
  toString := fun n => s!"{n}"
}

#check ToStr.instString

instance ToStr.instBool : ToStr Bool :=
  ⟨fun b => s!"{b}"⟩

#check ToStr.instBool

/-!
- `(a : α)` is an explicit parameter;
- `{a : α}` is implicit, must be inferrable from the other (explicit) arguments;
- `[a : Class]` is implicit, and is resolved by finding a suitable instance in the environment.
-/

#check ToStr.toString
#eval ToStr.toString true -- finds `ToStr.instBool` on its own
#eval ToStr.toString 7

/--
error: failed to synthesize instance
  ToStr (Option String)
-/
#guard_msgs in
  #eval ToStr.toString (some "cat")

/-! `instance`s are just regular functions, allowing to build "implications". -/

/-- Notice that typeclass parameters need not be named. -/
instance ToStr.instOption [ToStr α] : ToStr (Option α) where
  toString
  | none => "<none>"
  | some a => toString a -- need a `ToStr α` instance, which we have as a parameter

#eval ToStr.toString (some "cat")
#eval ToStr.toString (some 7)
#eval ToStr.toString (none : Option Bool)



/-! ## Your turn (again)

- `#check` out `Inhabited`
- write an instance for `L` (our list type, it's still there)

- `#check` out `ToString`, should look familiar
- write `L.toString` with the same signature as `ToString.toString`, probably using `L.foldl`
- write `L.instToString`, a `ToString` instance for `L`
-/

#check ToString
#check toString -- `ToString.toString` is directly in the prelude

section sol!
  namespace L

  instance instInhabited : Inhabited (L α) :=
    ⟨nl⟩

  /-- `protected` means that the function is never directly in scope.

  To refer to `toString`, we must write at least one namespace first: `L.toString`.

  Still allows "method-style" notation `l.toString` if `l : L α`, but it prevents from shadowing the
  `toString` that is already in the prelude.
  It does not matter much here, but it's good practice.
  -/
  protected def toString [ToString α] (self : L α) : String :=
    let start := "["
    let almost :=
      self.foldl start fun s elm =>
        let sep := if s = start then "" else ", "
        s!"{s}{sep}{elm}"
    almost ++ "]"

  instance instToString [ToString α] : ToString (L α) :=
    ⟨L.toString⟩

  end L
end sol!

-- getting super fancy
#check (inferInstance : ∀ (α : Type), Inhabited (L α))
#guard (default : L Nat) == .nl
#guard s!"{(L.nl : L Nat)}" == "[]"
#guard        s!"{L.test₁}" == "[0, 1, 2, 3]"



/-! Fun fact: we saw that `class` is a `structure`++, but we can do the same with `inductive`. -/

class inductive MeLike (α : Type)
| nothing
| thisValue : α → MeLike α

namespace MeLike

instance instBool : MeLike Bool := thisValue false
instance instNat : MeLike Nat := thisValue 7
instance instChar : MeLike Char := nothing

end MeLike

/-- Typeclass parameters can be named by the way. -/
def opinion [like? : MeLike α] [BEq α] [ToString α] (a : α) : String :=
  match like? with
  | .nothing => s!"I don't like `{a}`, but I like nothing in this type 😾"
  | .thisValue a' =>
    if a == a'
    then s!"I like value `{a}` 😻"
    else s!"`{a}` is terrible, I only like `{a'}` 😾"

#eval opinion true
#eval opinion false
#eval opinion 2
#eval opinion 7
#eval opinion 'z'
#eval opinion 'x'

/-! `class inductive` is almost exclusively used in the propositional (logics, ITP) parts of Lean 4.

`core` for instance only has **two** `class inductive`s, both propositional.
-/

#check Decidable
#check Nonempty
