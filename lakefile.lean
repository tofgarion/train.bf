import Lake
open Lake DSL

package «bf» where
  -- add package configuration options here

lean_lib «Bf» where
  -- add library configuration options here

require zen from git
  "https://github.com/anzenlang/zen" @ "v4.8.0"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "cf138201a0a4fa8ca78b6e2a42a0a4860369d10e"

@[default_target]
lean_exe bf where
  root := `Main
