import Bf.Part3



namespace Zen.Train.Bf




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

syntax "[" brnfck "]" : brnfck
syntax "[" "]" : brnfck
syntax brnfck brnfck : brnfck
syntax "![" term "]" : brnfck
syntax "echo!" "(" term ")" : brnfck
syntax "check!" "(" term "," term ")" : brnfck



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
| `( Bf.ast!( echo!($s) ) ) =>
  ``(Ast.dbg $s)
| `( Bf.ast!( check!($val, $msg) ) ) =>
  ``(Ast.chk $val $msg)



section elab!
  syntax (name := Bf.run)
    "Bf.run!"
        ("[" term "]")?
        "(" brnfck ")"
        ("[" term "]")?
  : term

  open Lean.Elab.Term (TermElab evalTerm)
  open Lean (mkApp mkConst levelZero)

  def typExtract' := mkConst ``Rt.Extract'
  def typNat := mkConst ``Nat
  def typAst := mkConst ``Ast
  def typArrayNat := mkApp (mkConst ``Array [levelZero]) typNat
  def typIOArrayNat := mkApp (mkConst ``IO []) typArrayNat
  def typExpr := mkConst ``Lean.Expr []
  def typIOExpr := mkApp (mkConst ``IO []) typExpr
  def typIOResExpr := mkApp (mkConst ``IO []) (mkApp (mkConst ``Rt.BfT.Res []) typExpr)
  def typListNat := mkApp (mkConst ``List [levelZero]) typNat

  @[term_elab Bf.run]
  unsafe def elabBfRun : TermElab := fun stx _expectedType? =>
    match stx with
    | `(
      Bf.run!
        $[[$ex:term]]?
        ($ast:brnfck)
        $[[$inputs:term]]?
    ) => do
      let inputs :=
        if let some inputs := inputs
        then inputs else ← `([])
      let ex ←
        if let some ex := ex then pure ex else `(Rt.Extract.array)
      let toRun ← `(Rt.BfT.justRunToExpr Rt.BfT.instSpecIO (M := IO) Bf.ast!($ast) $inputs $ex)
      let expr ← Lean.Elab.Term.elabTerm toRun none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← Lean.instantiateMVars expr
      let ioExpr? ← Lean.Meta.evalExpr (IO (Rt.BfT.Res Lean.Expr)) typIOResExpr expr
      let expr? ← ioExpr?
      match expr? with
      | .ok res _ => return res
      | .error e state =>
        let mem := state.mem.mapIdx fun idx val =>
          if idx = state.ptr then s!"*{val}*" else toString val
        IO.throwServerError s!"\
{e.toString}
- memory: {mem}\
        "
    | _ => Lean.Elab.throwUnsupportedSyntax
end elab!

#eval println! "=> `{Bf.ast!(..)}`"
example : Bf.ast!(.) = Ast.out :=
  rfl

#eval println! "=> `{Bf.ast!(+ +)}`"
example : Bf.ast!(—.) = Ast.seq #[.dec, .out] :=
  rfl

#eval
  let blah := Ast.Test.val1
  Bf.ast!(++![blah])

#check Bf.run!(+++.)
example : Bf.run!(+++.) = #[3] := by
  rfl

/-- error:
value check failed, expected `7`, got `3`: not 7 :/
- memory: #[*3*]
-/
#guard_msgs in #eval
  Bf.run![.array](+++.check!(7, "not 7 :/"))

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
error: [bf] failed to extract output `head!`, no output available
- memory: #[*3*]
-/
#guard_msgs in #eval
  Bf.run![.head!](+++)


example : Bf.run![.head!](
  check!(0, "@0 is 0 on init")
  +++++++
  check!(7, "added 1 × 7 to @0")
  [->+<]>
  check!(7, "copied 7@0 to @1")
  .
) = 7 :=
  rfl

#check Bf.ast!(.)
#eval Bf.ast!(>.,[],,..++—————)
#eval Rt.NoIO.justRun! (M := Id) Bf.ast!(,[->+<]>.) [8] .array
#eval
  let someCode := Bf.ast!([.++>————])
  Bf.ast!(>.,[],,.![someCode].++—————)

#eval
  Bf.run!(+++.)
#eval
  Bf.run!(, +++.)

/-- info:
entering loop
exiting loop
#[4]
-/
#guard_msgs in #eval
  Bf.ast!(
    ++++
    echo!("entering loop")
    [->+<]
    echo!("exiting loop")
    >.
    check!(4, "not 4 :/")
  ).evalIO! []
