import Lake
open Lake DSL

package «fixed-shift-liouville-critical-scale» where
  -- The single Lean file is intentionally kept at the repository root so that
  -- `lake build FixedShiftLiouville` checks exactly the same entry point as the
  -- supplied verification log.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib FixedShiftLiouville where
  roots := #[`FixedShiftLiouville]
