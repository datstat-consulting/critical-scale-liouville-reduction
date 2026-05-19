# Proof status

The included Lean entry point is:

```text
FixedShiftLiouville.lean
```

The last recorded successful check is archived at:

```text
logs/pass126_check.log
```

Static proof-debt scan for the checked source:

```text
axiom: 0
sorry: 0
admit: 0
```

The formalization verifies the deterministic reduction framework appearing in
the manuscript. This is the first half of the intended program: it reduces the
fixed-shift Liouville pair-correlation problem to critical-scale first-moment,
local-`U²`, and projected-packet criteria. The complementary analytic half—ruling
out the remaining Liouville-specific projected/local-`U²` packet obstruction—is
identified but not claimed as completed by this repository.
