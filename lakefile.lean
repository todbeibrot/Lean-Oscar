import Lake
open Lake DSL

package «oscar» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Mrdi» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Oscar» {
  -- add any library configuration options here
}
