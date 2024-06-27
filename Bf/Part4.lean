import Bf.Part3



/-! # Metaprogramming

Metaprogramming in Lean 4 is **deep**: Lean 4 is a reflexive language 🙀

- <https://leanprover-community.github.io/lean4-metaprogramming-book/main/01_intro.html>
-/
namespace Zen.Train.Bf



namespace Dsl



declare_syntax_cat brnfck

syntax ">" : brnfck
syntax ">>" : brnfck
syntax ">>>" : brnfck
syntax "<" : brnfck
syntax "<<" : brnfck
syntax "<<<" : brnfck
syntax "+" : brnfck
syntax "++" : brnfck
syntax "-" : brnfck
syntax "->" : brnfck
syntax "<-" : brnfck
syntax "+>" : brnfck
syntax ",+" : brnfck
syntax "—" : brnfck
syntax "——" : brnfck
syntax "." : brnfck
syntax ".." : brnfck
syntax "," : brnfck

syntax "[" brnfck ? "]" : brnfck
syntax brnfck brnfck : brnfck
syntax "![" term "]" : brnfck
syntax "dbg!" "(" term ")" : brnfck
syntax "chk!" "(" term "," term ")" : brnfck



/-- Syntax extension to create `Bf.Ast`-s. -/
syntax "Bf.ast!" "(" brnfck ")" : term

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
| `( Bf.ast!([$sub:brnfck]) ) =>
  ``( Ast.block Bf.ast!($sub) )
| `( Bf.ast!( $fst:brnfck $snd:brnfck ) ) => do
  ``( Ast.chain Bf.ast!($fst) Bf.ast!($snd) )
| `( Bf.ast!( ![$t] ) ) =>
  ``($t)
| `( Bf.ast!( dbg!($s) ) ) =>
  ``(Ast.dbg $s)
| `( Bf.ast!( chk!($val, $msg) ) ) =>
  ``(Ast.chk $val $msg)

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
    dbg!("entering loop")
    [->+<]
    dbg!("exiting loop")
    >.
    chk!(4, "not 4 :/")
  ).evalIO! []

/-- info:
#[4]
-/
#guard_msgs in #eval
  Bf.ast!(
    ++++
    dbg!("entering loop")
    [->+<]
    dbg!("exiting loop")
    >.
    chk!(4, "not 4 :/")
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



declare_syntax_cat brnfckRunOpt

syntax "-q" : brnfckRunOpt
syntax "-quiet" : brnfckRunOpt
syntax "-no-check" : brnfckRunOpt
syntax "-no-loop-limit" : brnfckRunOpt
syntax "-loop-limit" term:max : brnfckRunOpt

inductive RunOpt
| quiet
| noCheck
| loopLimit : Option Nat → RunOpt

namespace RunOpt

open Lean (TSyntax)
open Lean.Elab

unsafe def ofStx : TSyntax `brnfckRunOpt → TermElabM RunOpt
| `(brnfckRunOpt| -q)
| `(brnfckRunOpt| -quiet) => return quiet
| `(brnfckRunOpt| -no-check) => return noCheck
| `(brnfckRunOpt| -no-loop-limit) => return loopLimit none
| `(brnfckRunOpt| -loop-limit $l) => do
  let l ← Term.evalTerm Nat (Lean.mkConst ``Nat) l
  return loopLimit l
| _ => throwUnsupportedSyntax

def apply (config : Rt.Config) : RunOpt → Rt.Config
| quiet => {config with dbg := false}
| noCheck => {config with check := false}
| loopLimit l => {config with loopLimit := l}

unsafe def handleStxArray (opts : Array (TSyntax `brnfckRunOpt)) : TermElabM Rt.Config := do
  let mut conf := Rt.Config.default
  for opt in ← opts.mapM ofStx do
    conf := opt.apply conf
  return conf
end RunOpt



/-- `Bf.run! [extractor] ast [inputs]`

Runs `ast` with optionals `inputs`, and runs the optional `extractor` (`Extractor.array` if none).
-/
syntax (name := Bf.run)
  "Bf.run!" (brnfckRunOpt)*
    ("[" term "]")?
    "(" brnfck ")"
    ("[" term "]")?
: term



section elab!

open Lean.Elab.Term (TermElab evalTerm)
open Lean (mkApp mkConst levelZero)

def typNat := mkConst ``Nat
def typExpr := mkConst ``Lean.Expr
def typElabResExpr := mkApp (mkConst ``Lean.Elab.TermElabM) (mkApp (mkConst ``Rt.BfT.Res) typExpr)
def typListNat := mkApp (mkConst ``List [levelZero]) typNat

@[term_elab Bf.run]
unsafe def elabBfRun : TermElab := fun stx _expectedType? =>
  match stx with
  | `(
    Bf.run!
      -- $[$opts:brnfckRunOpt]*
      $[[$ex:term]]? ($ast:brnfck) $[[$inputs:term]]?
  ) => do
    -- let conf ← RunOpt.handleStxArray opts
    let inputs :=
      if let some inputs := inputs
      then inputs else ← `([])
    let ex ←
      if let some ex := ex then pure ex else ``(Rt.Extract.array)
    let toRun ← ``(Rt.Elab.runExtractExpr Bf.ast!($ast) $inputs $ex)
    let expr ← Lean.Elab.Term.elabTerm toRun none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← Lean.instantiateMVars expr
    let elabExpr ←
      Lean.Meta.evalExpr (Lean.Elab.TermElabM (Rt.BfT.Res Lean.Expr)) typElabResExpr expr
    let expr? ← elabExpr
    match expr? with
    | .ok res _ => return res
    | .error e state =>
      let mem := state.mem.mapIdx fun idx val =>
        if idx = state.ptr then s!"*{val}*" else toString val
      Lean.throwError m!"{e.toString}\n- memory: {mem}"
  | _ => Lean.Elab.throwUnsupportedSyntax
end elab!

example : Bf.run!(+++.) = #[3] := by
  rfl

/-- info:
done
-/
#guard_msgs in example : Bf.run!(![Ast.Test.val1]) = #[2] := by
  rfl

/-- error:
value check failed, expected `7`, got `3`: not `7` :/
- memory: [*3*]
-/
#guard_msgs in #eval
  Bf.run![.array](+++.chk!(7, "not `7` :/"))

example : Bf.run![.head?](+++.) = some 3 :=
  rfl
example : Bf.run![.head?](+++) = none :=
  rfl
example : Bf.run![.head!](+++.) = 3 :=
  rfl

/-- info:
I 🖤 catz
俺も
-/
#guard_msgs in #eval do
  let array : Array String :=
    Bf.run![.string] (,[.>,]) [
      ("I 🖤 catz".data |>.map Char.toNat)
      ++ [10^10] -- not a legal char, acts as a separator
      ++ ("俺も".data |>.map Char.toNat)
    ]
  for s in array do
    println! s

/-- error:
[bf] failed to extract output `head!`, no output available
- memory: [*3*]
-/
#guard_msgs in #eval
  Bf.run![.head!](+++)


example : Bf.run![.head!](
  chk!(0, "@0 is 0 on init")
  +++++++
  chk!(7, "added 1 × 7 to @0")
  [->+<]>
  chk!(7, "copied 7@0 to @1")
  .
) = 7 :=
  rfl

#eval
  Bf.run!(+++.)
#eval
  Bf.run!(, +++.)
