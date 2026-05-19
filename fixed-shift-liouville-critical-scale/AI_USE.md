# AI-use disclosure

AI tools (ChatGPT 5.5 Plus Extended Thinking) were used in a limited, assistive capacity for this repository. The
repository is presented as the first, deterministic-reduction half of the
project; AI assistance was not used to assert or certify an unconditional proof
of the remaining analytic obstruction.

Permitted uses in this project:

1. Lean proof engineering: proof repair, API migration, tactic cleanup, and
   checking that the submitted Lean file contains no `sorry`, `admit`, or
   `axiom` declarations.
2. Literature review assistance: locating and organizing relevant references
   and background context.
3. TeX cleanup and polishing: correcting notation, exposition, cross-references,
   theorem-roadmap consistency, and manuscript formatting.
4. Error correction: identifying mismatches between the TeX exposition and the
   Lean formalization, including the replacement of the incorrect linear local-
   `U²` estimate by the fourth-power/Young-inequality route.

AI tools were not used as an independent mathematical authority. All statements,
proofs, and claims remain the responsibility of the author. In particular, the
formal Lean artifact is included so that the mechanically checked deterministic
part of the work can be inspected directly. The repository does not present the
remaining Liouville-specific analytic obstruction as solved.

The current Lean check log records:

- Lean version: 4.29.1
- entry point: `FixedShiftLiouville.lean`
- `sorry`: 0
- `admit`: 0
- `axiom`: 0
- Lean exit code: 0, with warnings only
