import Bf

open Zen.Train.Bf in
def main (_args : List String) : IO Unit := do
  for n in [0:30] do
    let config :=
        .allOff
        -- { Rt.Config.allOff with dbg := true }

    -- -- stack overflow :/
    -- let res ←
    --   Zen.Train.Bf.Std.fibOfInput.evalIOTo! [n] .head! config

    -- no stack overflow :)
    let res ←
      Zen.Train.Bf.Std.fibOfInput.fastEvalIOTo! [n] .head! config

    println! "fib {n} := {res}"
