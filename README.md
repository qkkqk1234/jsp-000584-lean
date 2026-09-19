# JSP-000584 — Lean 4 formalization

**Problem.** Must every regular graph of the specified degree contain a
three-regular subgraph?

**Result formalized.** Alon–Friedland–Kalai, *Every 4-regular graph plus an edge
contains a 3-regular subgraph*, J. Combin. Theory Ser. B **37** (1984), 92–93.

**Contribution.** Formalization only. The mathematics is due to Alon, Friedland
and Kalai; see `PRIOR_ART.md`.

## Headline theorem

`JSP584.exists_three_regular_of_four_regular_multigraph_add_edge` — every
4-regular loopless multigraph plus one edge contains a nonempty 3-regular
subgraph. See `STATEMENT.md` for why multigraphs, and not `SimpleGraph`, are the
faithful setting.

## Proof

The paper's Chevalley–Warning argument, formalized as stated:

1. Give each edge a variable over `ZMod 3`; for each vertex `v` form the
   quadratic form summing `x_e ^ 2` over the edges at `v`, of total degree `2`.
2. When there are more than `2 · #V` edges, `mathlib`'s
   `char_dvd_card_solutions_of_fintype_sum_lt` makes the number of common zeros
   divisible by `3`. The zero assignment is one, so a nonzero common zero exists.
3. Over `ZMod 3` squaring is the indicator of being nonzero, so the support `S`
   meets every vertex in a multiple of `3` edges.
4. Maximum degree `≤ 5` forces that count to be `0` or `3`.

Steps 1–3 are `JSP584/Core.lean` and contain no graph theory: the core lemma takes
only an incidence assignment `inc : V → Finset E`. That is what lets the same core
serve both the multigraph and the `SimpleGraph` layer.

## Layout

| File | Contents |
|---|---|
| `JSP584/Core.lean` | Chevalley–Warning core, graph-free |
| `JSP584/Multigraph.lean` | the faithful AFK statement and its general form |
| `JSP584/Simple.lean` | `SimpleGraph` specialisation |
| `JSP584/Audit.lean` | axiom audit and a non-vacuity witness |
| `evidence/build.log` | clean build transcript |
| `evidence/axioms.log` | `#print axioms` for every result |

## Verification

```
lake exe cache get
lake build JSP584
```

Pinned: Lean `v4.34.0`; `mathlib` `5ed2965256430c3649e86755f9576b54eca72435`
(tag `v4.34.0`), with all transitive revisions in `lake-manifest.json`.

`scripts/verify.sh` runs a clean build, greps the sources for `sorry`, `admit`,
`native_decide`, `unsafe`, `implemented_by` and custom `axiom` declarations, and
re-runs the axiom audit.

Every result depends on exactly `[propext, Classical.choice, Quot.sound]` — the
three standard `mathlib` axioms, with no `sorryAx` and no `native_decide`.

## Submitter

GitHub: [@qkkqk1234](https://github.com/qkkqk1234)
