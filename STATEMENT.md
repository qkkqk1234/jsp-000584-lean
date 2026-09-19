# Statement fidelity — JSP-000584

## The problem as recorded

> Must every regular graph of the specified degree contain a three-regular subgraph?

Source credited in the problem bank:

> N. Alon, S. Friedland, G. Kalai, *Every 4-regular graph plus an edge contains a
> 3-regular subgraph*, J. Combin. Theory Ser. B **37** (1984), 92–93.

## Formal statement

The headline theorem is `JSP584.exists_three_regular_of_four_regular_multigraph_add_edge`
in `JSP584/Multigraph.lean`:

```lean
theorem exists_three_regular_of_four_regular_multigraph_add_edge
    (ends : E → Sym2 V) (hnd : ∀ e, ¬ (ends e).IsDiag)
    (hreg : ∀ v, mdeg ends v = 4) {a b : V} (hab : a ≠ b) :
    ∃ S : Finset (E ⊕ Unit), S.Nonempty ∧
      ∀ v, mdegOn (addEdge ends a b) S v = 0 ∨ mdegOn (addEdge ends a b) S v = 3
```

## Why multigraphs, not `SimpleGraph`

This is the main modelling decision, and it is forced.

The companion paper (*Regular subgraphs of almost regular graphs*, JCTB **37**
(1984), 79–91) states on p. 79 that "all graphs considered are finite,
undirected, and contain no loops… Note that we **allow multiple edges**", and on
p. 80 that the Berge–Sauer conjecture fails for graphs with parallel edges — an
odd cycle with every edge doubled is 4-regular with no 3-regular subgraph — and
therefore "the 'plus one edge' cannot be omitted in (1.1)".

So multiple edges are exactly what makes the hypothesis non-redundant. For
*simple* graphs Taškinov's theorem already yields a 3-regular subgraph with no
extra edge, so a simple-graph-only formalization would capture a strictly weaker
statement that a stronger known theorem subsumes. The multigraph version is
therefore the faithful one.

A multigraph is modelled by its incidence map `ends : E → Sym2 V`. Looplessness
is `¬ (ends e).IsDiag`; parallel edges are distinct `e₁ ≠ e₂` with
`ends e₁ = ends e₂`, which the model permits. "Plus one edge" is the index type
`E ⊕ Unit`, with the extra index sent to `s(a, b)`.

## Why an edge set encodes "3-regular subgraph"

The conclusion produces `S : Finset E` with every vertex meeting `S` in `0` or
exactly `3` edges. That is precisely the edge set of a 3-regular subgraph: take
the vertices of `S`-degree `3` as the vertex set. No edge is left dangling,
because an edge of `S` with endpoint `v` forces that count to be at least `1`,
hence equal to `3`.

`mathlib` has `SimpleGraph.Subgraph.degree` but no `Subgraph.IsRegularOfDegree`,
and no multigraph subgraph API at all, so the edge-set form is stated directly.
That the conclusion is non-degenerate is itself proved, for the simple-graph
version, as `JSP584.exists_incidence_card_eq_three`: a nonempty `S` really forces
a vertex of `S`-degree exactly `3`.

## Non-vacuity

`JSP584Audit.witness` instantiates the simple-graph corollary at the octahedron
`K₂,₂,₂` on `Fin 6` (`a ~ b` iff `a % 3 ≠ b % 3`), with the added edge `s(0, 3)`.
`Oct.IsRegularOfDegree 4`, `¬ Oct.Adj 0 3` and `(0 : Fin 6) ≠ 3` are all closed by
`decide`. Six vertices is the smallest possible witness: no 4-regular simple
graph exists on `≤ 4` vertices, and on `5` vertices the only one is `K₅`, which
has no non-adjacent pair.

## Contents

| Theorem | File | Content |
|---|---|---|
| `exists_nonempty_inter_card_mod_three` | `Core.lean` | Chevalley–Warning core, no graph theory |
| `exists_three_regular_multigraph` | `Multigraph.lean` | max degree `≤ 5`, more than `2·#V` edges |
| `sum_mdeg_eq_twice` | `Multigraph.lean` | handshake lemma for the incidence model |
| `exists_three_regular_multigraph_type45` | `Multigraph.lean` | AFK (1.1): degrees in `{4,5}`, some vertex `5` |
| `exists_three_regular_of_four_regular_multigraph_add_edge` | `Multigraph.lean` | **the paper's statement** |
| `exists_three_regular_edge_set` | `Simple.lean` | simple-graph specialisation |
| `exists_three_regular_of_four_regular_add_edge` | `Simple.lean` | simple-graph corollary |
| `exists_three_regular_of_four_regular_add_edge'` | `Simple.lean` | instance-free restatement |
| `exists_incidence_card_eq_three` | `Simple.lean` | conclusion is non-degenerate |
| `witness` | `Audit.lean` | hypotheses are satisfiable |

## Known limitations

1. The `SimpleGraph` statements are a special case, for the reason given above.
   They are retained because they are phrased in `mathlib`'s native API; the
   multigraph theorem is the one that matches the paper.
2. `Simple.lean` locally disables the instance `SimpleGraph.fintypeEdgeSetSup`,
   because `Fintype (G ⊔ H).edgeSet` is reachable by two routes. `Fintype` is a
   subsingleton, so both routes give propositionally equal `Finset`s and the
   meaning of the statement is unchanged; only elaboration is affected. The
   primed restatement `exists_three_regular_of_four_regular_add_edge'` avoids
   `edgeFinset` and `incidenceFinset` entirely, needs no such option, and is what
   downstream users should apply.
3. The mathematics is entirely due to Alon, Friedland and Kalai; see
   `PRIOR_ART.md`. Only the formalization is contributed here.
