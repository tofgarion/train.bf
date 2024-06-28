import Bf

open Zen.Train.Bf

def main (_args : List String) : IO Unit := do
  for n in [0:30] do
    let config := .allOff
    -- let config := .default

    -- stack overflow :/
    let res ←
      Zen.Train.Bf.Std.fib.evalIOTo! [n] .head! config

    -- -- no stack overflow :)
    -- let res ←
    --   Zen.Train.Bf.Std.fib.fastEvalIOTo! [n] .head! config

    println! "fib {n} := {res}"
