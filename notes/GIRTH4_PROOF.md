# Conjecture 144 — Complete human proof for girth four

## Status

Human proof complete. Lean formalization remains open.

Let

- `q = ecc G G.center`,
- `D = diam G`, and
- `t = largestInducedTreeSize G`.

Assume throughout that `G` is finite, simple, connected, and has girth four.
We prove

```text
t >= q + 3.
```

This is exactly Conjecture 144 when `girth G = 4`.

## Checked ingredients

The current Lean development already proves:

1. `D + 1 <= t`, from a diametral geodesic.
2. `q <= D`.
3. When `q = 0`, Conjecture 144.
4. When a diametral geodesic has an outside vertex with exactly one neighbor on
   the geodesic, adjoining that vertex gives an induced tree on `D + 2`
   vertices.

The branch `proof/positive-center-depth-v2` contains the next metric lemma:

```text
q > 0  ->  q + 1 <= D.
```

Its mathematical proof is complete and it is being kernel-checked separately.

## Reduction to the tight metric case

If `q = 0`, the checked center-depth-zero theorem applies.

Suppose `q > 0`. Then `q + 1 <= D`.

- If `q + 2 <= D`, the diametral-geodesic tree has order
  `D + 1 >= q + 3`, so the result follows.
- It remains only to consider

```text
D = q + 1.
```

We prove that in this case some diametral geodesic has an outside vertex with
exactly one neighbor on it. The checked geodesic-extension theorem then gives

```text
t >= D + 2 = q + 3.
```

## Contrapositive structural lemma

We prove the stronger contrapositive:

> If no diametral geodesic has an outside vertex with exactly one neighbor on
> it, then `q <= D - 2`.

This contradicts `D = q + 1` and proves the required existence statement.

Fix a diametral geodesic

```text
P = v_0, v_1, ..., v_D.
```

Because `P` is geodesic, it is induced.

### Lemma 1: neighbor pattern on a geodesic

Let `x` lie outside `P` and suppose it has two neighbors `v_i` and `v_j` on
`P`, with `i < j`.

The two-edge walk `v_i - x - v_j` shows

```text
dist(v_i, v_j) <= 2.
```

The subpath of a geodesic is geodesic, so

```text
dist(v_i, v_j) = j - i.
```

Hence `j - i <= 2`.

Since the graph has no triangle, `j - i != 1`. Therefore

```text
j = i + 2.
```

The same argument rules out three path neighbors: among three indices with no
consecutive pair, the first and last differ by at least four, contradicting the
two-edge shortcut. Thus an outside vertex with at least two path neighbors has
exactly two, of the form

```text
v_i and v_(i+2).
```

It is the opposite corner of a 4-cycle over the path segment
`v_i - v_(i+1) - v_(i+2)`.

### Lemma 2: every diametral geodesic is dominating

Assume no diametral geodesic has a uniquely attached outside vertex.

Suppose some vertex has distance at least two from `P`. Choose a shortest path
to `P`, and let

- `z` be the vertex at distance one from `P`, and
- `w` its predecessor, at distance two from `P`.

The vertex `z` has a neighbor on `P`. By the no-extension assumption it cannot
have exactly one path neighbor. By Lemma 1, its path neighbors are exactly
`v_i` and `v_(i+2)` for some `i`.

Replace `v_(i+1)` in `P` by `z`:

```text
P' = v_0, ..., v_i, z, v_(i+2), ..., v_D.
```

This is a path of the same length `D`; hence it is another diametral geodesic.
The vertex `w` is outside `P'`. Because `w` was at distance two from the
original `P`, it has no neighbor on any original path vertex. It is adjacent to
`z`, so it has exactly one neighbor on `P'`.

This contradicts the no-extension assumption. Therefore every vertex is at
distance at most one from `P`: the diametral geodesic is dominating.

### Lemma 3: midpoint vertices are central

By domination and the no-extension assumption, every vertex outside `P` has
exactly two path neighbors `v_i` and `v_(i+2)`.

Let

```text
R = ceil(D / 2).
```

Choose a midpoint vertex of `P`, say `m = v_floor(D/2)`.

- Every path vertex is within distance `R` of `m`.
- An outside vertex adjacent to `v_i` and `v_(i+2)` is also within distance
  `R` of `m`: use the closer of its two path neighbors. The only local peak is
  when `m = v_(i+1)`, in which case the distance is two, and `2 <= R` whenever
  `D >= 3`.

Thus `ecc(m) <= R`.

On the other hand, for every vertex `c`, the triangle inequality applied to the
diametral endpoints gives

```text
D = dist(v_0, v_D)
  <= dist(v_0, c) + dist(c, v_D)
  <= 2 * ecc(c).
```

Therefore every eccentricity is at least `ceil(D/2) = R`. Hence `m` is a
center vertex. When `D` is odd, the same proof makes both middle path vertices
central.

### Lemma 4: center depth is at most `D - 2`

If `D >= 4`, every vertex is within `R = ceil(D/2)` of the central midpoint,
and

```text
ceil(D/2) <= D - 2.
```

Hence `q <= D - 2`.

If `D = 3`, both middle vertices `v_1` and `v_2` are central. Every path vertex
is adjacent to one of them. Every outside vertex is adjacent either to
`v_0, v_2` or to `v_1, v_3`, and therefore is also adjacent to a center vertex.
Thus

```text
q <= 1 = D - 2.
```

If `D = 2`, triangle-freeness rules out a universal vertex: a universal vertex
together with any edge of the 4-cycle would make a triangle. Consequently every
vertex has eccentricity two, the center is the whole vertex set, and

```text
q = 0 = D - 2.
```

This completes the contrapositive structural lemma.

## Conclusion

In the tight case `D = q + 1`, the contrapositive lemma forbids the absence of
a one-neighbor diametral extension. Therefore such an extension exists, and the
checked extension construction yields

```text
t >= D + 2 = q + 3.
```

Hence Conjecture 144 holds for every connected graph of girth four.

## Formalization plan

1. Formalize the geodesic neighbor-index lemma:
   two path neighbors of an outside vertex on a geodesic differ by at most two.
2. Use girth four to sharpen the pattern to exactly `i` and `i+2`.
3. Formalize the path replacement `v_(i+1) -> z` and domination argument.
4. Formalize midpoint eccentricity at most `ceil(D/2)`.
5. Prove the three diameter cases and assemble the exact girth-four theorem.
