import Bf.Part3



/-! # Metaprogramming

Metaprogramming in Lean 4 is **deep**: Lean 4 is a reflexive language 🙀

- <https://leanprover-community.github.io/lean4-metaprogramming-book/main/01_intro.html>
-/
namespace Zen.Train.Bf



namespace Dsl



declare_syntax_cat bfTerm

/-- Creates a `Bf.Ast`-s.

Notes:
- use `—` (`\em`) instead of `-` to avoid `--` being a comment;
- `![ast]` injects the term `ast : Ast`;
- `(dbg! string)` to build `Ast.dbg string`;
- `(chk! nat string)` to build `Ast.chk nat string`.
-/
syntax "Bf.ast!" "(" bfTerm ")" : term

syntax ">" : bfTerm
syntax ">>" : bfTerm
syntax ">>>" : bfTerm
syntax "<" : bfTerm
syntax "<<" : bfTerm
syntax "<<<" : bfTerm
syntax "+" : bfTerm
syntax "++" : bfTerm
syntax "-" : bfTerm
syntax "->" : bfTerm
syntax "<-" : bfTerm
syntax "+>" : bfTerm
syntax ",+" : bfTerm
syntax "—" : bfTerm
syntax "——" : bfTerm
syntax "." : bfTerm
syntax ".." : bfTerm
syntax "," : bfTerm

syntax "[" bfTerm ? "]" : bfTerm
syntax bfTerm bfTerm : bfTerm
syntax "![" term "]" : bfTerm
syntax "(" "dbg!" term ")" : bfTerm
syntax "(" "chk!" term:max term ")" : bfTerm
syntax "(" "dump!" ")" : bfTerm

macro_rules
| `(Bf.ast!(>)) => ``(Ast.mvr)
| `(Bf.ast!(<)) => ``(Ast.mvl)
| `(Bf.ast!(+)) => ``(Ast.inc)
| `(Bf.ast!(—)) => ``(Ast.dec)
| `(Bf.ast!(-)) => ``(Ast.dec)
| `(Bf.ast!(.)) => ``(Ast.out)
| `(Bf.ast!(,)) => ``(Ast.inp)
| `(Bf.ast!(——)) => ``(Ast.seqN 2 Ast.dec)
| `(Bf.ast!(->)) => ``(Ast.seq #[Ast.dec, Ast.mvr])
| `(Bf.ast!(<-)) => ``(Ast.seq #[Ast.mvl, Ast.dec])
| `(Bf.ast!(+>)) => ``(Ast.seq #[Ast.inc, Ast.mvr])
| `(Bf.ast!(>>)) => ``(Ast.seqN 2 Ast.mvr)
| `(Bf.ast!(<<)) => ``(Ast.seqN 2 Ast.mvl)
| `(Bf.ast!(>>>)) => ``(Ast.seqN 3 Ast.mvr)
| `(Bf.ast!(<<<)) => ``(Ast.seqN 3 Ast.mvl)
| `(Bf.ast!(++)) => ``(Ast.seqN 2 Ast.inc)
| `(Bf.ast!(..)) => ``(Ast.seqN 2 Ast.out)
| `(Bf.ast!(,+)) => ``(Ast.seq #[Ast.inp, Ast.inc])
| `( Bf.ast!([]) ) =>
  ``( Ast.block <| Ast.seq #[] )
| `( Bf.ast!([$sub:bfTerm]) ) =>
  ``( Ast.block Bf.ast!($sub) )
| `( Bf.ast!( $fst:bfTerm $snd:bfTerm ) ) => do
  ``( Ast.chain Bf.ast!($fst) Bf.ast!($snd) )
| `( Bf.ast!( ![$t] ) ) =>
  ``($t)
| `( Bf.ast!( (dbg! $s) ) ) =>
  ``(Ast.dbg $s)
| `( Bf.ast!( (chk! $val $msg) ) ) =>
  ``(Ast.chk $val $msg)
| `( Bf.ast!( (dump!) ) ) =>
  ``(Ast.dump)

example : Bf.ast!(.) = Ast.out :=
  rfl
example : Bf.ast!(..) = Ast.seqN 2 .out :=
  rfl
example : Bf.ast!(—.) = Ast.seq #[.dec, .out] :=
  rfl

/-- info: >.,[],,..++----- -/
#guard_msgs in #eval Bf.ast!(>.,[],,..++—————)
/-- info: >.,[],,.[.++>----].++----- -/
#guard_msgs in #eval
  let someCode := Bf.ast!([.++>————])
  Bf.ast!(>.,[],,.![someCode].++—————)

/-- info: #[8] -/
#guard_msgs in #eval
  Bf.ast!(,[->+<]>.).evalTo! [8] .array

/-- info:
entering loop
exiting loop
#[4]
-/
#guard_msgs in #eval
  Bf.ast!(
    ++++
    (dbg! "entering loop")
    [->+<]
    (dbg! "exiting loop")
    >.
    (chk! 4 "not 4 :/")
  ).evalIO! []

/-- info:
#[4]
-/
#guard_msgs in #eval
  Bf.ast!(
    ++++
    (dbg! "entering loop")
    [->+<]
    (dbg! "exiting loop")
    >.
    (chk! 4 "not 4 :/")
  ).eval! []

end Dsl



namespace Rt

def BfT.handleSeffElab : Ast.Seff → BfT Lean.Elab.Term.TermElabM Unit
| .dbg msg => do
  Lean.logInfo msg
| seff =>
  handleSeff seff

protected instance Elab : Spec (BfT Lean.Elab.Term.TermElabM) :=
  { Rt.NoIO with seff := BfT.handleSeffElab }

def Spec.runExtractExpr
  [Monad M] [Inhabited α] [Lean.ToExpr α]
  (S : Spec (BfT M)) (code : Ast) (inputs : List Nat) (ex : Extract α)
: M (BfT.Res Lean.Expr) := do
  let res ← S.exe code inputs ex
  return Lean.ToExpr.toExpr <$> res

end Rt



namespace Dsl

export Lean.Elab.Term (evalTerm)

unsafe def evalTerm' (α : Type) [I : Lean.ToExpr α] (stx : Lean.Syntax) :=
  Lean.Elab.Term.evalTerm α I.toTypeExpr stx

unsafe def evalTerm'' {α : Type} [Lean.ToExpr α] := evalTerm' α



namespace Ty
open Lean (mkConst mkApp Expr)

def nat := mkConst ``Nat
def expr := mkConst ``Expr
def bool := mkConst ``Bool

def res (t : Expr) := mkApp (mkConst ``Rt.BfT.Res) t
def list (t : Expr) := mkApp (mkConst ``List [Lean.levelZero]) t
def option (t : Expr) := mkApp (mkConst ``Option [Lean.levelZero]) t

def typElabResExpr := mkApp (mkConst ``Lean.Elab.TermElabM) (res expr)
def listNat := list nat
def optionNat := option nat
end Ty



declare_syntax_cat bfOption (behavior := symbol)

syntax "verb" " := " term : bfOption
syntax "check" " := " term : bfOption
syntax "loopLimit" " := " term : bfOption



inductive Options
| verb : Bool → Options
| check : Bool → Options
| loopLimit : Option Nat → Options

namespace Options

open Lean (TSyntax)
open Lean.Elab

unsafe def ofStx : TSyntax `bfOption → TermElabM Options
| `(bfOption| verb := $v) => do
  let v ← evalTerm'' v
  return Options.verb v
| `(bfOption| check := $c) => do
  let c ← evalTerm'' c
  return Options.check c
| `(bfOption| loopLimit := $limit) => do
  try
    let l ← evalTerm'' limit
    return Options.loopLimit (some l)
  catch
  | _ =>
    let l ← evalTerm'' limit
    return Options.loopLimit l
| _ => throwUnsupportedSyntax

def apply (config : Rt.Config) : Options → Rt.Config
| verb b => {config with dbg := ¬ b}
| check c => {config with check := c}
| loopLimit l => {config with loopLimit := l}

unsafe def stxArrayToConfig (opts : Array (TSyntax `bfOption)) : TermElabM Rt.Config := do
  let mut conf := Rt.Config.default
  for opt in ← opts.mapM ofStx do
    conf := opt.apply conf
  return conf
end Options



declare_syntax_cat bfExtractor (behavior := symbol)

syntax "array" : bfExtractor
syntax "unit" : bfExtractor
syntax "head?" : bfExtractor
syntax "head!" : bfExtractor
syntax "strings" : bfExtractor
syntax "string" : bfExtractor



namespace Extractor
open Lean.Elab (TermElabM)
open Lean (Expr ToExpr TSyntax)

def applyExtractor [I : ToExpr α] (ex : Rt.Extract α) (desc : String) (outputs : Array Nat)
: TermElabM Expr :=
  match ex.apply outputs with
  | .ok res => return I.toExpr res
  | .error e => Lean.throwError s!"[{desc} extractor] {e}"

def apply (state : Rt.State) : Lean.TSyntax `bfExtractor → TermElabM Expr
| `(bfExtractor| unit) =>
  applyExtractor .unit "unit" state.outputs
| `(bfExtractor| array) =>
  applyExtractor .array "array" state.outputs
| `(bfExtractor| head?) =>
  applyExtractor .head? "head?" state.outputs
| `(bfExtractor| head!) =>
  applyExtractor .head! "head!" state.outputs
| `(bfExtractor| string) =>
  applyExtractor .string "string" state.outputs
| `(bfExtractor| strings) =>
  applyExtractor .strings "strings" state.outputs
| _ => Lean.Elab.throwUnsupportedSyntax
end Extractor


/-- `Bf.run! <options> to <extractor> bf(<ast>) <inputs>`

Runs `ast` on `inputs`, extracting the result with `extractor`.

- `<options>` is potentially empty sequence of
  - `(verb := b)` with `b : Bool`
  - `(dbg := b)` with `b : Bool`
  - `(loopLimit := n?)` with `n? : Nat`

- `to <extractor>` is optional (`Extract.array` if none), with `<extractor>` one of `unit`, `array`,
  `head?`, `head!`, `strings`, `string`.

- `<inputs>` is the optional list of input, `[]` if none.
-/
syntax (name := Bf.run)
  "Bf.run!"
    ( "(" bfOption ")" )*
    ( "to " bfExtractor )?
    ( ("!" "(" bfTerm ")" ) <|> term:max )
    term ?
: term

-- dealing with `bfExtractor` default
macro_rules
| `(Bf.run! $[($opts)]* !($bf)) =>
  `(Bf.run! $[($opts)]* to array !($bf) [])

| `(Bf.run! $[($opts)]* !($bf) $inputs) =>
  `(Bf.run! $[($opts)]* to array !($bf) $inputs)

| `(Bf.run! $[($opts)]* to $ex !($bf)) =>
  `(Bf.run! $[($opts)]* to $ex !($bf) [])

| `(Bf.run! $[($opts)]* to $ex !($bf:bfTerm) $inputs) =>
  `(Bf.run! $[($opts)]* to $ex Bf.ast!($bf) $inputs)



section elab!

open Lean.Elab.Term (TermElab)
open Lean (mkApp mkConst levelZero)

@[term_elab Bf.run]
unsafe def elabBfRun : TermElab := fun stx _expectedType? =>
  match stx with
  | `(
    Bf.run!
      $[ ( $opts:bfOption ) ]*
      to $extractor:bfExtractor
      $ast:term
      $inputs:term
  ) => do
    let inputs ← evalTerm' (List Nat) inputs
    -- Lean.logInfo s!"inputs: {inputs}"
    let config ← Options.stxArrayToConfig opts
    -- Lean.logInfo s!"ast: {ast}"
    let ast ← evalTerm Ast (mkConst ``Ast) ast
    -- Lean.logInfo s!"ast: {ast}"
    -- set up runtime state with appropriate inputs
    let initState := Rt.State.mk inputs (config := config)
    -- run the code
    match ← Rt.Elab.justRun ast initState with
    | .ok () finalState =>
      -- run the extractor
      Extractor.apply finalState extractor
    | .error e s =>
      -- code failed, report error
      Lean.throwError m!"\
{e}
- memory:\n{s.prettyMem "  | "}
- inputs left: {s.inputs}
- outputs: {s.outputs}\
      "
  | _ => Lean.Elab.throwUnsupportedSyntax
end elab!

example : Bf.run! !(+++.) = #[3] := by
  rfl

/-- info:
done
-/
#guard_msgs in example : Bf.run! !( ![Ast.Test.val1] ) = #[2] := by
  rfl

/-- error:
value check failed, expected `7`, got `3`: not `7` :/
- memory:
  | *0* ↦ 3
- inputs left: []
- outputs: [3]
-/
#guard_msgs in #eval
  Bf.run! to array !(+++. (chk! 7 "not `7` :/"))

example : Bf.run! to head? !(+++.) = some 3 :=
  rfl
example : Bf.run! to head? !(+++) = none :=
  rfl
example : Bf.run! to head! !(+++.) = 3 :=
  rfl

/-- error: [head! extractor] expected at least one output, found none -/
#guard_msgs in #eval
  Bf.run! to head! !(+++)

/-- info:
I 🖤 catz
俺も
-/
#guard_msgs in #eval do
  let array : Array String :=
    Bf.run! to strings !(,[.>,])
      (
        ("I 🖤 catz".data |>.map Char.toNat)
        ++ [10^10] -- not a legal char, acts as a separator
        ++ ("俺も".data |>.map Char.toNat)
      )
  for s in array do
    println! s

/-- error: [head! extractor] expected at least one output, found none -/
#guard_msgs in #eval
  Bf.run! to head! !(+++)


example : Bf.run! to head!
  !(
    (chk! 0 "@0 is 0 on init")
    +++++++
    (chk! 7 "added 1 × 7 to @0")
    [->+<]>
    (chk! 7 "copied 7@0 to @1")
    .
  )
  = 7
:=
  rfl


def fib7 := Bf.run! to head! !( ![Std.fibOfInput] ) [7]

#eval Lean.ToExpr.toExpr fib7
