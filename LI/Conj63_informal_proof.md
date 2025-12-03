# Informal Proof of Conjecture 6.3

**Note:** This informal proof was AI-generated based on the formal proof found in `Conj63.lean`.

## Theorem Statement

Let $k$ be a positive integer and $n = 2k$. For any $p \in (0, 1/2)$, let $\sigma = \sqrt{p(1-p)}$.
The conjecture states that:

$$ 1 - \Phi\left(\frac{(1/2-p)\sqrt{n}}{\sigma}\right) + \frac{1}{2}\binom{n}{k}\sigma^n \le \mathbb{P}[B(n, p) \ge k] $$

where $\Phi$ is the cumulative distribution function (CDF) of the standard normal distribution, and $B(n, p)$ denotes a binomial random variable with parameters $n$ and $p$.

## Proof Overview

The proof proceeds by defining a "gap" function representing the difference between the right-hand side (binomial tail) and the left-hand side (corrected Gaussian approximation). We show that this gap function is non-negative on the interval $(0, 1/2)$.

### 1. Integral Representation of the Binomial Tail

First, the tail probability of the binomial distribution is identified with an integral representation using the Incomplete Beta Function. Specifically, for $n=2k$:

$$ \mathbb{P}[B(n, p) \ge k] = n \binom{n-1}{k-1} \int_0^p t^{k-1}(1-t)^{n-k} dt $$

This allows us to treat the discrete sum as a continuous, differentiable function of $p$ (see `binomial_tail_eq_integral`).

### 2. Definition of the Gap Function

We define the gap function $f_{ext}(p)$ as:

$$ f_{ext}(p) = \text{BinomialTail}(n, k, p) - \left( 1 - \Phi\left(\frac{(1/2-p)\sqrt{n}}{\sigma}\right) + \frac{1}{2}\binom{n}{k}\sigma^n \right) $$

We aim to show $f_{ext}(p) \ge 0$ for $p \in (0, 1/2)$.

### 3. Boundary Conditions

We examine the behavior of $f_{ext}(p)$ at the boundaries of the interval $(0, 1/2)$:

*   **At $p \to 0$:** It is shown that $\lim_{p \to 0^+} f_{ext}(p) = 0$ (see `gap_limit_at_zero`).
*   **At $p = 1/2$:** It is shown that $f_{ext}(1/2) = 0$. This involves checking that the binomial integral simplifies to $1/2$ plus a correction term that exactly cancels the Gaussian correction term (since the Gaussian argument becomes 0, $\Phi(0) = 1/2$) (see `gap_at_half_eq_zero`).

### 4. Derivative Analysis

To determine the sign of $f_{ext}(p)$, we analyze its derivative with respect to $p$. The derivative is computed as:

$$ f'_{ext}(p) = \frac{1}{2}\binom{2k}{k} k [p(1-p)]^{k-1} + \phi(z) \cdot z' $$

where $z = \frac{(1/2-p)\sqrt{2k}}{\sqrt{p(1-p)}}$, $\phi$ is the standard normal PDF, and $z'$ is the derivative of $z$ with respect to $p$ (see `deriv_gap_decompose`).

### 5. The Auxiliary Function $\psi$

The sign of the derivative $f'_{ext}(p)$ is shown to be equivalent to the condition $\psi(p) \ge C$ for a specific auxiliary function $\psi$ and constant $C$. Specifically:

$$ \psi(p) = \frac{z^2}{2} + (k + 1/2)\log(p(1-p)) $$
$$ C = \log\left( \frac{\sqrt{k}}{4\sqrt{\pi} \cdot \frac{1}{2}\binom{2k}{k}k} \right) $$

The proof establishes that $f'_{ext}(p) \ge 0 \iff \psi(p) \ge C$ (see `deriv_gap_sign_iff_psi`).

### 6. Unimodality and Sign Pattern

It is proven that $\psi(p)$ crosses the threshold $C$ exactly once in the interval $(0, 1/2)$. There exists a critical value $c \in (0, 1/2)$ such that:
*   For $0 < p < c$, $\psi(p) \ge C \implies f'_{ext}(p) \ge 0$.
*   For $c \le p < 1/2$, $\psi(p) \le C \implies f'_{ext}(p) \le 0$.

This means the gap function $f_{ext}(p)$ is increasing on $(0, c]$ and decreasing on $[c, 1/2)$.

### 7. Conclusion

Since $f_{ext}(p)$ starts at 0 (limit at 0), increases, and then decreases to 0 (value at 1/2), it must be non-negative throughout the entire interval $(0, 1/2)$. This confirms the conjecture.

$$ f_{ext}(p) \ge 0 \implies \text{Conjecture holds.} $$

