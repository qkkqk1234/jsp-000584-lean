# Prior art and attribution

## The mathematics is not ours

The theorem formalized here is due to:

> N. Alon, S. Friedland, G. Kalai,
> *Every 4-regular graph plus an edge contains a 3-regular subgraph*,
> Journal of Combinatorial Theory, Series B **37** (1984), 92–93.

The proof strategy formalized here — assigning an `F_3` variable to each edge,
forming one quadratic form per vertex, and invoking the Chevalley–Warning
theorem — is exactly the argument of that paper. No part of the mathematical
content originates with this submission.

Related earlier work recorded in the problem bank:

> V. A. Taškinov, *Regular subgraphs of regular graphs*,
> Soviet Math. Dokl. (1982), 37–38.

## What is ours

Only the Lean 4 formalization: the statement encoding, the `mathlib`
development, and the verification artifacts in this directory.

Submitted as a **formalization** contribution (`Lean formalizer`), not as a
solver contribution. The solver credit belongs to Alon, Friedland and Kalai.

## Independence

The formalization was written directly from the published argument. At the time
of submission no Lean formalization of JSP-000584 was present in this
repository or, to the submitter's knowledge, in `mathlib`. In particular
`mathlib` contains no notion of a `3`-regular subgraph obtained this way, and no
Chevalley–Warning application to graph theory.

## Submitter

GitHub: [@qkkqk1234](https://github.com/qkkqk1234)
