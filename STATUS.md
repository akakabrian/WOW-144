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

The dependency is pinned to Formal Conjectures commit
`e923379e609b9d5987011a1d1f06ec22ea25cd20` and Lean `v4.27.0`.

`ecc G G.center` is the maximum distance of a non-center vertex from the
nearest center vertex, with value zero when every vertex is central.

### OPEN

No exact general proof has yet replaced the upstream `sorry`.

### NEXT

Close the remaining empty-3-core multicyclic case, then formalize the exact theorem.

## SEARCH

### PROVEN

- Exact exhaustive search over all 995 connected unlabeled graphs on 2–7
  vertices found no counterexample.  See `search/exhaustive_atlas.py` and
  `search/exhaustive_atlas_summary.json`.
- A seeded adversarial deletion test checked 8,830 connected graphs of girth at
  least five and cycle rank at least two, through order 100, with zero failures.
  See `search/test_deletion_lemma.py` and `search/test_deletion_lemma.json`.
- The tempting shortcut
  `tree ≥ girth - 1 + floor((path - 1)/2)` is false; balanced theta witnesses
  are preserved in `search/refute_path_plus_girth_bound.*`.

### OPEN

Computational evidence is not a proof of the remaining deletion lemma.
Earlier exploratory graph counts not backed by a preserved artifact are not
part of the authoritative evidence package.

### NEXT

Stress and prove the deletion lemma only in the mathematically remaining class:
connected, girth at least five, cycle rank at least two, and empty 3-core.

## PROOF

### PROVEN

Human proofs have been completed for:

1. **Acyclic graphs.**  The girth term is zero and the graph itself is an
   induced tree.
2. **Center depth zero.**  A shortest cycle with one vertex removed is an
   induced tree of order `girth - 1`.
3. **Center depth one.**  For girth at least five, attach one outside vertex to
   a shortest cycle and delete a different cycle vertex; girth forces unique
   attachment.  Low girth is handled by induced-path bounds.
4. **All unicyclic graphs.**  A complete weighted-cycle/branch proof is in the
   local evidence package, validated on 7,834 unicyclic graphs through order 40.
5. **Graphs with nonempty 3-core, in the hard range.**  An induced minimum-degree
   three core has girth at least that of the graph.  For girth five, a shortest
   5-cycle plus two forced outside neighbors yields a 6-vertex induced tree.
   For girth at least six, a radius-`floor((g-2)/2)` ball is an induced tree and
   minimum degree three gives at least `3*2^k-2 ≥ 2g-4` vertices.  This covers
   `girth - 1 + centerDepth` once `centerDepth ≤ girth - 3`.

### OPEN

The remaining class is:

- girth at least five;
- center depth at least two and at most `girth - 3`;
- cycle rank at least two;
- empty 3-core (subdivision-like / 2-degenerate structure).

Leading candidate lemma:

> Some vertex can be deleted while preserving connectedness, girth, and not
> decreasing center depth.

Induction would then reduce the graph to the proved unicyclic case.

### NEXT

Prove the candidate by selecting globally among degree-two threads in the
2-core/block structure.  Arbitrary degree-two deletion is known to be false,
so the proof must use a global extremal choice.

## LEAN

### PROVEN

The isolated repository contains no-`sorry` candidate support files:

- `WOW144/Audit.lean`
- `WOW144/Arithmetic.lean`
- `WOW144/InducedTree.lean`

A workflow modeled on the successful `WOW-146` workflow has been installed.

### OPEN

No GitHub Actions run or `lean-ci.log` has appeared after connector-created
main pushes, proof-branch pushes, or an issue trigger.  The local runtime has no
Lean executable.  Therefore **nothing in WOW-144 has yet been kernel-checked**.

The likely cause is that GitHub suppresses workflow triggering for events made
through the installed app/token, or Actions has not yet been enabled manually
for the new repository.

### NEXT

Run `Verify WOWII 144` manually from the repository Actions page, or make one
ordinary user-authored push.  Once a log exists, fix Lean errors iteratively and
record exact exit status.

## REVIEW

### PROVEN

False auxiliary lemmas and their witnesses have been preserved rather than
silently discarded.  The original conjecture survived every preserved bounded
search.

### OPEN

The unicyclic and 3-core human proofs require an independent line-by-line proof
review.  No independent Lean review is possible until CI runs.

### NEXT

Adversarially review the global deletion lemma and the reduction to the hard
range before claiming a complete proof.

## SUBMISSION

### PROVEN

No upstream checkout, Conjecture 146 artifact, pull request, or maintainer
contact has been modified or initiated.

### OPEN

The conjecture is not solved or candidate solved.

### NEXT

Do not publish or submit without Brian's explicit approval after exact Lean
kernel checking and independent review.
