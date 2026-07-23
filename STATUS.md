# WOW II Conjecture 144 — Status

## STATEMENT

### PROVEN

The exact authoritative theorem is preserved unchanged:

```lean
theorem conjecture144 (G : SimpleGraph α) (h : G.Connected) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  sorry
```

The isolated project is pinned to Formal Conjectures commit
`e923379e609b9d5987011a1d1f06ec22ea25cd20` and Lean `v4.27.0`.

`ecc G G.center` is the maximum distance from a non-center vertex to the
nearest center vertex, with value zero if every vertex is central.

### OPEN

No exact unrestricted proof has replaced the authoritative upstream
placeholder. The project proves substantial exact subclasses only.

### NEXT

Close the remaining cyclic center-depth-at-least-two range, then assemble and
kernel-check the exact unrestricted theorem.

## SEARCH

### PROVEN

- Exhaustive search over all 995 connected unlabeled graphs on 2–7 vertices
  found no counterexample. See `search/exhaustive_atlas.py` and
  `search/exhaustive_atlas_summary.json`.
- A seeded adversarial deletion test checked 8,830 connected graphs of girth at
  least five and cycle rank at least two, through order 100, with zero failures.
  See `search/test_deletion_lemma.py` and `search/test_deletion_lemma.json`.
- False shortcuts are retained with witnesses. In particular,
  `tree ≥ girth - 1 + floor((path - 1)/2)` is false; see
  `search/refute_path_plus_girth_bound.*`.

### OPEN

Computational evidence is not a proof of the remaining deletion lemma.
Exploratory counts without preserved scripts and outputs are not authoritative
project evidence.

### NEXT

Concentrate search on the mathematically unresolved class: connected cyclic
graphs with center depth at least two, especially multicyclic graphs with empty
3-core and long degree-two threads.

## PROOF

### PROVEN — LEAN KERNEL CHECKED

The exact Conjecture 144 inequality is proved for:

1. **Every connected acyclic graph.** The formal proof combines
   `ecc G G.center ≤ G.diam` with an induced diametral geodesic of order
   `G.diam + 1`.
2. **Center depth zero.** Deleting one vertex from a girth-realizing cycle gives
   an induced tree on exactly `girth - 1` vertices.
3. **Center depth one, all girths.** The proof covers:
   - girth three via the diametral-geodesic bound;
   - girth four via a diameter-two contradiction producing a triangle;
   - girth at least five via a nearest path to a shortest cycle and the unique
     cycle-attachment construction.
4. Therefore the exact theorem is proved whenever
   `ecc G G.center ≤ 1`.

Reusable checked results include:

- every explicit finite induced tree is bounded by `largestInducedTreeSize`;
- `G.girth - 1 ≤ largestInducedTreeSize G` for cyclic graphs;
- `G.diam + 1 ≤ largestInducedTreeSize G` for connected graphs;
- `ecc G G.center ≤ G.diam`;
- a shortest cycle covering every vertex forces `G.center = Set.univ`;
- one unique outside attachment to a shortest cycle yields an induced tree on
  `girth` vertices.

### PROVEN — HUMAN / NOT YET FORMALIZED

A human weighted-cycle argument has been developed for unicyclic graphs, and a
separate large-core argument has been developed for the nonempty-3-core part of
the hard range. These are not counted as Lean-verified results and still need
independent line-by-line review before formalization.

### OPEN

After the checked cases, the principal unresolved range is cyclic graphs with
center depth at least two. The computationally supported induction candidate is:

> Some vertex can be deleted while preserving connectedness and girth and
> without decreasing center depth.

Arbitrary degree-two deletion is false, so any proof must choose globally among
threads or blocks.

### NEXT

1. Kernel-check the branch theorem that positive center depth satisfies
   `ecc G G.center + 1 ≤ G.diam`; it would prove the full girth-three class.
2. Prove the center-depth-preserving deletion lemma or replace it with a direct
   weighted-kernel/block decomposition.
3. Formalize the unicyclic argument only after independent proof review.

## LEAN

### PROVEN

The main branch currently contains and builds:

- `WOW144/Audit.lean`
- `WOW144/Arithmetic.lean`
- `WOW144/InducedTree.lean`
- `WOW144/CycleBase.lean`
- `WOW144/CycleAttachment.lean`
- `WOW144/CycleCover.lean`
- `WOW144/Geodesic.lean`
- `WOW144/NearestCycle.lean`
- `WOW144/MetricBounds.lean`
- `WOW144/SmallGirth.lean`
- `WOW144/CenterDepthOne.lean`

The authoritative `lean-ci.log` records:

- the pinned upstream Conjecture 144 module built successfully;
- all local modules built with warnings treated as errors;
- the complete `WOW144` target built successfully in 8,052 jobs;
- all printed local theorems depend only on Lean's standard logical
  foundations (`propext`, `Classical.choice`, and `Quot.sound`);
- the local `sorry`/`axiom` scan found no prohibited declarations or
  placeholders;
- final `EXIT_STATUS=0`.

### OPEN

The unrestricted theorem is not a Lean artifact. The branch
`proof/positive-center-depth` contains the next metric extension and is being
checked independently.

### NEXT

After the branch passes, port its two theorems to `main`, run a fresh clean
build, and then continue with the center-depth-at-least-two structural lemma.

## REVIEW

### PROVEN

- False auxiliary lemmas and their witnesses are preserved rather than silently
  discarded.
- The exact theorem statement has not been weakened or changed.
- The checked subclass proofs have auditable compiler output and no local
  placeholders.

### OPEN

- The unicyclic and nonempty-3-core human proofs need independent review.
- The deletion lemma remains computationally supported but unproved.
- A separate review pass is required before any upstream submission package.

### NEXT

Review the positive-depth diameter proof after CI, then adversarially review the
remaining block/thread reduction.

## SUBMISSION

### PROVEN

No upstream checkout, Conjecture 146 artifact, upstream pull request, or
maintainer communication has been modified or initiated.

### OPEN

Conjecture 144 is not solved or candidate solved in full.

### NEXT

Do not publish or submit upstream without Brian's separate explicit approval
after the exact unrestricted theorem passes Lean and receives independent
review.
