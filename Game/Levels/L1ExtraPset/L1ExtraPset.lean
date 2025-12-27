import Game.Metadata

World "L1ExtraPset"


Level 1
Title "Problem 1"

Introduction "# Problem 1"

/-- Given that `g (u) = u^2 + 2 * u` for all `u`, prove that there exists some `a` such that `g (3) = a`. -/
Statement (g : ℝ → ℝ) (h : ∀ u, g u = u ^ 2 + 2 * u) :
  ∃ (a : ℝ), g 3 = a := by
  use 15
  specialize h 3
  rewrite [h]
  ring_nf

Conclusion "Done."

Level 2
Title "Problem 2"

Introduction "# Problem 2"

/-- Given that `h (x) = 4 * x - 2` for all `x`, prove that there exists some `x` such that `h (x) = 10`. -/
Statement (h : ℝ → ℝ) (h_eq : ∀ x, h x = 4 * x - 2) :
  ∃ x, h x = 10 := by
  use 3
  specialize h_eq 3
  rewrite [h_eq]
  ring_nf

Conclusion "Done."

Level 3
Title "Problem 3"

Introduction "# Problem 3"

/-- Given `f(x) = x + 5` and `g(x) = 3 * x`, prove that there exists an `a` equal to `f(g(2))`. -/
Statement (f g : ℝ → ℝ) (hf : ∀ x, f x = x + 5) (hg : ∀ x, g x = 3 * x) :
  ∃ a, f (g 2) = a := by
  use 11
  rewrite [hg]
  rewrite [hf]
  ring_nf

Conclusion "Done."

Level 4
Title "Problem 4"

Introduction "# Problem 4"

/-- Given that `k (x) = 3 * x + 1` for all `x`, prove that there exists some `x` such that `k (x) = 16`. -/
Statement (k : ℝ → ℝ) (hk : ∀ x, k x = 3 * x + 1) :
  ∃ x, k x = 16 := by
  use 5
  specialize hk 5
  rewrite [hk]
  ring_nf

Conclusion "Done."


Level 5
Title "Sum of Evens"

Introduction "
# Number Theory: Even Numbers

In real mathematics, we define an integer $n$ to be **even** if there exists some integer $k$ such that $n = 2k$.

**Theorem:** The sum of two even integers is even.

**Proof Strategy:**
1. `choose` the witnesses for $a$ and $b$ (unpack the definition of even).
2. `use` the sum of those witnesses to prove $a+b$ is even.
3. `ring_nf` to show the algebra works.
"

/-- Let $a$ and $b$ be integers. If $a$ is even and $b$ is even, then $a+b$ is even. -/
Statement (a b : ℤ) (ha : ∃ k, a = 2 * k) (hb : ∃ k, b = 2 * k) :
  ∃ k, a + b = 2 * k := by
  choose k1 hk1 using ha
  choose k2 hk2 using hb
  use k1 + k2
  rewrite [hk1]
  rewrite [hk2]
  ring_nf

Conclusion "Q.E.D. (Quod Erat Demonstrandum). You have proven a standard number theory result!"

Level 6
Title "Product of Odds"

Introduction "
# Number Theory: Odd Numbers

An integer $n$ is **odd** if there exists some integer $k$ such that $n = 2k + 1$.

**Theorem:** The product of two odd integers is odd.

This is slightly harder algebra, but `ring_nf` will handle it for you. Focus on the logic: unpack the hypotheses, find the new witness, and solve.
"

/-- Let $a$ and $b$ be integers. If $a$ is odd and $b$ is odd, then $a \cdot b$ is odd. -/
Statement (a b : ℤ) (ha : ∃ k, a = 2 * k + 1) (hb : ∃ k, b = 2 * k + 1): 
  ∃ k, a * b = 2 * k + 1 := by
  choose k1 hk1 using ha
  choose k2 hk2 using hb
  use 2 * k1 * k2 + k1 + k2
  rewrite [hk1]
  rewrite [hk2]
  ring_nf

Conclusion "Nice. If you did this by hand, you'd have to expand `(2k+1)(2j+1)` manually. Lean does the heavy lifting!"


Level 7
Title "Problem 7"

Introduction "# Complex Existence

We are now working with the Complex Numbers, denoted by `ℂ`.
The imaginary unit is written as `Complex.I`.

Proving things in `ℂ` works exactly the same as in `ℝ`. `ring_nf` is smart enough to know how to handle `Complex.I`.
"
/-- Given that `f(z) = z + Complex.I` for all `z`, prove that there exists a `w` such that `f(w) = 3 * Complex.I`. -/
Statement (f : ℂ → ℂ) (h : ∀ z, f z = z + Complex.I) :
  ∃ w, f w = 3 * Complex.I := by
  use 2 * Complex.I
  rewrite [h]
  ring_nf

Conclusion "
Done.
Note: If you were wondering, `ring_nf` knows that `2 * I + I` is `3 * I`.
"
