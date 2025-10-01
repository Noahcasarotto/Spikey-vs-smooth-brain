import Lake
open Lake DSL

package «spikey-vs-smooth-brain» where
  -- add package configuration options here

lean_lib «SpikyVsSpherical» where
  -- add library configuration options here

@[default_target]
lean_exe «spikey-vs-smooth-brain» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

