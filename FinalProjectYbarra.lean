import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Topology.MetricSpace.Basic

/-

For my final project I will be proving the theorem from my analysis
class last quarter (142a) found in Elementary Analysis, The Theory of Calculus by Kenneth A. Ross:

10.11 Theorem.
A sequence is a convergent sequence if and only if it is a Cauchy sequence.

My original project was to be a graph theory theorem but I had a lot of difficulty in formalizing
the proof not using certrain mathlib theorems. The use of these theorems made the proofs trivial but
proving these theorems from scratch was very difficult and would take a lot more time than I have to
complete the project so I decided to pivot to a theorem that I have some more experience with
proving from scratch.

Included in this project are helper theorems and lemmas that are necessary for the proof.
The backwards direction of this proof takes a different strategy than Ross though. Ross uses limit
infimum and limit supremum in his proof which would require lots of background formalization from
scratch. So, I decided to formalize the Cauchy → Convergent direction using the Bolzano Wierstrass
Theorem. I have left this as a black box axiomly since it is a nontrivial proof using a 'peak'
argument in the textbook. References in README.md

-/


/- 10.8 Definition.
A sequence (sn) of real numbers is called a Cauchy sequence if
for each ϵ > 0 there exists a number N such that
m,n > N implies |sn−sm| < ϵ.
-/
def Is_Cauchy (sₙ : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, n > N → m > N → |sₙ n - sₙ m| < ε


/- 7.1 Definition
A sequence(sn) of real numbers is said to converge to the real number
s provided that for each ϵ > 0 there exists a number N such that
n > N implies |sn−s| < ϵ.
-/
def Is_Convergent (sₙ : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N → |sₙ n - s| < ε


/- 9.0 Definition
A sequence (sn) of real numbers is said to be bounded
if the set {sn : n ∈ N} is a bounded set, i.e., if there exists a constant
M such that |sn| ≤ M for all n.
-/

def Is_Bounded (sₙ : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, |sₙ n| ≤ M


/- 11.5 Bolzano-Weierstrass Theorem.
Every bounded sequence has a convergent subsequence.
*φ* is the notation of a subsequence
-/
axiom bolzano_weierstrass (sₙ : ℕ → ℝ) (hB : Is_Bounded sₙ) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l : ℝ, Is_Convergent (sₙ ∘ φ) l


/- 9.1 Theorem.
Convergent sequences are bounded.
-/

theorem convergent_is_bounded (sₙ : ℕ → ℝ) (s : ℝ) :
  Is_Convergent sₙ s → Is_Bounded sₙ := by
  intro hconv
  -- ε = 1 then n > N → |sₙ n - s| < 1
  have ⟨N, hN⟩ := hconv 1 one_pos
  -- From the triangle inequality we see n > N implies |sₙ n| < |s| + 1
  have htri : ∀n > N, |sₙ n| ≤ |s| + 1 := by
    intro n hn
    have h_eps := hN n hn
    calc
      |sₙ n| = |(sₙ n - s) + s| := by ring_nf
      _ ≤ |(sₙ n - s)| + |s| := abs_add_le (sₙ n - s) s
      _ ≤  1 + |s| := by linarith
      _ = |s| + 1 := by ring
  --To find a maximum of a finite set, first must prove the set is not empty
  have hnonempty : (Finset.range (N+1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  -- Define M = max{|s|+1,|s1|,|s2|,...,|sN|}.
  let M_seq := ((Finset.range (N+1)).sup' hnonempty (fun i => |sₙ i|))
  let M := max M_seq (|s| + 1)
  use M
  intro n
  -- Then we have |sn| ≤ M
  by_cases hn : n > N
  · exact le_max_of_le_right (htri n hn)
  · push Not at hn
    exact le_max_of_le_left
      (Finset.le_sup' (fun i => |sₙ i|)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))


/-
10.9 Lemma.
Convergent sequences are Cauchy sequences.

This theorem encodes the theorem from Ross' analysis textbook that says convergent sequences are
cauchy sequences. First the theorem formalization assumes that the seqeunce sₙ (the input sequence)
is convergent to s (the input limit). The lean code also assumes there is an ε and that ε > 0.
-/

theorem convergent_is_cauchy (sₙ : ℕ → ℝ) (s : ℝ) :
  Is_Convergent sₙ s → Is_Cauchy sₙ := by
  intro hconv ε hε
  -- ε/2 is > 0 using the mathlib theorem half_pos
  have hεhalf : (ε / 2) > 0 := by
      exact half_pos hε
  -- exists N for which n > N the distance between the sequence and s is less than ε/2 by convergent
  have hsε : ∃ N : ℕ, ∀ n > N, |sₙ n - s| < ε / 2 :=
    hconv (ε / 2) hεhalf
  rcases hsε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  --  there is a n and m such that
  intro n m hn hm
  have h₁ : |sₙ n - s| < ε / 2 := hN n hn
  have h₂ : |sₙ m - s| < ε / 2 := hN m hm
  calc
    |sₙ n - sₙ m|
    -- |sₙ n - sₙ m| is equivalent to |(sₙ n - s) + (s - sₙ m)|
        = |(sₙ n - s) + (s - sₙ m)| := by ring_nf
        -- ≤ |sₙ n - s| + |s - sₙ m| by the triangle inequality
    _ ≤ |sₙ n - s| + |s - sₙ m| :=
        abs_add_le (sₙ n - s) (s - sₙ m)
    _ = |sₙ n - s| + |sₙ m - s| := by
      simp [abs_sub_comm]
      -- < ε/2 + ε/2 = ε
    _ < ε / 2 + ε / 2 := by
          exact add_lt_add h₁ h₂
    _ = ε := by
          ring

/-
10.10 Lemma.
Cauchy sequences are bounded.

This is a formalization of the the theorem from Ross' textbook that states that cauchy
sequences are bounded. The code assumes that the input sequence is cauchy.
-/

theorem cauchy_is_bounded (sₙ : ℕ → ℝ) :
  Is_Cauchy sₙ → Is_Bounded sₙ := by
  intro hcauchy
  have hε1 :
  --ε = 1, since any ε > 0 works : ε = 1 > 0 (by Real.zero_lt_one)
    ∃ N : ℕ, ∀ n m : ℕ, n > N → m > N → |sₙ n - sₙ m| < 1 := by
    have := hcauchy 1 (by exact Real.zero_lt_one)
    simpa using this
    --∀ (n m : ℕ), n > N → m > N → |sₙ n - sₙ m| < 1
  rcases hε1 with ⟨N, hN⟩
  -- By triangle inequality, |sₙ n| = |(sₙ n - sₙ(N+1)) + sₙ(N+1)| ≤ |sₙ n - sₙ(N+1)| + |sₙ(N+1)|
  -- Since n and N+1 are both > N, the distance between them is < 1, so |sₙ n| < |sₙ(N+1)| + 1.
  have hb : ∀ n > N, |sₙ n| ≤ |sₙ (N+ 1)| + 1 := by
    intro n hn
    have h := hN n (N +1)
    grind
    ---- To find a maximum of a finite set, first must prove the set is not empty
  have hnonempty : (Finset.range (N + 1)).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  -- maximum absolute value among the first N elements indicies (0-N)
  let M_seq := (Finset.range (N + 1)).sup' hnonempty (fun i => |sₙ i|)
  -- max of max value in indicies 0-N and (|sₙ (N+1)| + 1)
  let M := max M_seq (|sₙ (N+1)| + 1)
  -- M bounds all elements in the sequence
  have hbound : ∀ n : ℕ, |sₙ n| ≤ M := by
    intro n
    by_cases hn : n > N
    · have : |sₙ n| ≤ |sₙ (N+1)| + 1 := hb n hn
      exact le_max_of_le_right this
    · push Not at hn -- n ≤ N
      have hmem : n ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
      have : |sₙ n| ≤ M_seq :=
        Finset.le_sup' (fun i => |sₙ i|) hmem
      exact le_max_of_le_left this
  -- M bounds the sequence
  exact ⟨M, hbound⟩


/- (fact from 142a)
In a strictly monotone subsequence φ : ℕ → ℕ satisfies φ n ≥ n for all n.
This is needed in the cauchy → convergent argument to ensure the subsequence index
φ n is large enough to apply the Cauchy condition.
-/
lemma strictMono_ge (φ : ℕ → ℕ) (hφ : StrictMono φ) : ∀ n, n ≤ φ n := by
  intro n
  induction n with
  | zero      => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))


/-
If (sₙ) is Cauchy and a subsequence (sₙ ∘ φ) converges to l,
then the whole sequence converges to l.
-/
theorem cauchy_subseq_limit (sₙ : ℕ → ℝ) (hC : Is_Cauchy sₙ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (l : ℝ)
    (hconv : Is_Convergent (sₙ ∘ φ) l) :
    Is_Convergent sₙ l := by
  intro ε hε -- ε > 0
  have hε2 : ε / 2 > 0 := half_pos hε
  -- n'ε from subsequence convergence: n > n'ε → |sₙ(φ n) - l| < ε/2
  obtain ⟨n'ε,  hn'⟩  := hconv (ε / 2) hε2
  -- n''ε from Cauchy condition: n,m > n''ε → |sₙ n - sₙ m| < ε/2
  obtain ⟨n''ε, hn''⟩ := hC   (ε / 2) hε2
  -- N = max{n'ε, n''ε}
  use max n'ε n''ε
  intro n hn
  have hn'ε  : n > n'ε  := lt_of_le_of_lt (le_max_left  _ _) hn
  have hn''ε : n > n''ε := lt_of_le_of_lt (le_max_right _ _) hn
  -- φ n ≥ n > n''ε, so both n and φ n are past the Cauchy threshold
  have hφn_gt : φ n > n''ε :=
    lt_of_lt_of_le hn''ε (strictMono_ge φ hφ n)
  -- |sₙ n - l| ≤ |sₙ n - sₙ(φ n)| + |sₙ(φ n) - l| < ε/2 + ε/2 = ε
  calc |sₙ n - l|
      = |(sₙ n - sₙ (φ n)) + (sₙ (φ n) - l)| := by ring_nf
    _ ≤ |sₙ n - sₙ (φ n)| + |sₙ (φ n) - l|   := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add
      -- |sₙ n - sₙ(φ n)| < ε/2 by Cauchy since n, φ n > n''ε
        · exact hn'' n (φ n) hn''ε hφn_gt
      -- |sₙ(φ n) - l| < ε/2 by subsequence convergence since n > n'ε
        · exact hn' n hn'ε
    _ = ε := by ring


/-
10.11 Theorem
Every Cauchy sequence converges.

This theorem formalizes the backward direction of Ross' 10.11. First, by Ross 10.10
(cauchy_is_bounded) the Cauchy sequence is bounded. Then by the Bolzano-Weierstrass
theorem (Ross 11.5) the bounded sequence has a convergent subsequence (sₙ ∘ φ) with
limit l. Finally, cauchy_subseq_limit proves the whole sequence converges to l using
the triangle inequality argument: since φ n ≥ n, for n large enough both n and φ n
are past the Cauchy threshold, so |sₙ n - l| < ε.
-/

theorem cauchy_is_convergent (sₙ : ℕ → ℝ) (hC : Is_Cauchy sₙ) :
    ∃ s : ℝ, Is_Convergent sₙ s := by
  -- By Ross 10.10 every Cauchy sequence is bounded
  have hB : Is_Bounded sₙ := cauchy_is_bounded sₙ hC
  -- By Bolzano-Weierstrass (Ross 11.5) every bounded sequence has a convergent subsequence
  obtain ⟨φ, hφ_strict, ⟨a, ha⟩⟩ := bolzano_weierstrass sₙ hB
  -- The whole sequence converges to the same limit by cauchy_subseq_limit
  exact ⟨a, cauchy_subseq_limit sₙ hC φ hφ_strict a ha⟩

/-
10.11 Theorem.
A sequence is a convergent sequence if and only if it is a Cauchy
sequence.

This theorem encodes the full biconditional from Ross' textbook. The forward direction
follows from convergent_is_cauchy (Ross 10.9). The backward direction follows from
cauchy_is_convergent which uses cauchy_is_bounded (Ross 10.10), Bolzano-Weierstrass
(Ross 11.5), and cauchy_subseq_limit.
-/
theorem convergent_iff_cauchy (sₙ : ℕ → ℝ) :
    (∃ s : ℝ, Is_Convergent sₙ s) ↔ Is_Cauchy sₙ := by
  constructor
  · rintro ⟨s, hs⟩
    exact convergent_is_cauchy sₙ s hs
  · intro hcauchy
    exact cauchy_is_convergent sₙ hcauchy
