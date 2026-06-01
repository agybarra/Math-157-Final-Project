import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Bounds.Basic

/-

For my final project I will be proving the theorem from my analysis
class last quarter (142a) found in Elementary Analysis, The Theory of Calculus by Kenneth A. Ross:

10.11 Theorem.
A sequence is a convergent sequence if and only if it is a Cauchy
sequence.

My original project was to be a graph theory theorem but I had a lot of difficulty in formalizing
the proof not using certrain mathlib theorems. The use of these theorems made the proofs trivial but
proving these theorems from scratch was very difficult and would take a lot more time than I have to
complete the project so I decided to pivot to a theorem that I have some more experience with
proving from scratch.

So, I will be formalizing both directions of this theorem, and potentially adding more theorems to
build from if time permits. In addition to this theorem I will be proving helper theorems and other
relevant theorems.
-/


/- 10.8 Definition.
A sequence (sn) of real numbers is called a Cauchy sequence if
for each ϵ > 0 there exists a number N such that
m,n > N implies |sn−sm| < ϵ.

This definition encodes the definition of a Cauchy sequence from the Ross textbook above.
-/
def Is_Cauchy (sₙ : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, n > N → m > N → |sₙ n - sₙ m| < ε


/-
A sequence (sn) of real numbers is said to be bounded
if the set {sn : n ∈ N} is a bounded set, i.e., if there exists a constant
M such that |sn| ≤ M for all n.

This definition encodes the definition of a bounded sequence from the Ross textbook above.

-/

def Is_Bounded (sₙ : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, |sₙ n| ≤ M


/-
A sequence(sn) of real numbers is said to converge to the real number
s provided that for each ϵ > 0 there exists a number N such that
n > N implies |sn−s| < ϵ.

This definition encodes the definition of a convergent sequence from the Ross textbook above.

-/

def Is_Convergent (sₙ : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N → |sₙ n - s| < ε



/- 9.1 Theorem.
Convergent sequences are bounded.

This theorem encodes the theorem from Ross' analysis textbook
-/

theorem convergent_is_bounded
  (s : ℝ) :
  Is_Convergent sₙ s → Is_Bounded sₙ := by
  sorry


/-
10.9 Lemma.
Convergent sequences are Cauchy sequences.

This theorem encodes the theorem from Ross' analysis textbook that says convergent sequences are
cauchy sequences. First the theorem formalization assumes that the seqeunce sₙ (the input sequence)
is convergent to s (the input limit). The lean code also assumes there is an ε and that ε > 0. Then
the code then proves that ε/2 is > 0 using the mathlib theorem half_pos which says that if a number
a > 0 then a/2 > 0. Then the code proves that there exists an N for which n > N the distance
between the sequence and s is less than ε/2 through the convergent hypothesis. Then, given a fixed N
in ℕ there is a n and m such that |sₙ n - s| < ε / 2 and |sₙ m - s| < ε / 2. Then, the proof
calculates that |sₙ n - sₙ m| is equivalent to |(sₙ n - s) + (s - sₙ m)| by rewriting which is
≤ |sₙ n - s| + |s - sₙ m| by the triangle inequality which is < ε/2 + ε/2 = ε and thus
|sₙ n - sₙ m| < ε which is the definition of cauchy. This follows Ross' proof in the textbook and
formalized it.
-/

theorem convergent_is_cauchy (sₙ : ℕ → ℝ) (s : ℝ) :
  Is_Convergent sₙ s → Is_Cauchy sₙ := by
  intro hconv ε hε
  have hεhalf : (ε / 2) > 0 := by
      exact half_pos hε
  have hsε : ∃ N : ℕ, ∀ n > N, |sₙ n - s| < ε / 2 :=
    hconv (ε / 2) hεhalf
  rcases hsε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n m hn hm
  have h₁ : |sₙ n - s| < ε / 2 := hN n hn
  have h₂ : |sₙ m - s| < ε / 2 := hN m hm
  calc
    |sₙ n - sₙ m|
        = |(sₙ n - s) + (s - sₙ m)| := by ring_nf
    _ ≤ |sₙ n - s| + |s - sₙ m| :=
        abs_add_le (sₙ n - s) (s - sₙ m)
    _ = |sₙ n - s| + |sₙ m - s| := by
      simp [abs_sub_comm]
    _ < ε / 2 + ε / 2 := by
          exact add_lt_add h₁ h₂
    _ = ε := by
          ring

/-
10.10 Lemma.
Cauchy sequences are bounded.

This code is a formalization of the the theorem from Ross' textbook that states that cauchy
sequences are bounded. The code starts out by assuming that the unput sequence is cauchy. Then,
following Ross' proof of the theorem, the code chooses and proves that one can have ε = 1 since
it is cauchy and any ε > 0 works, so if ε = 1 it is greater than 0 (by Real.zero_lt_one). Then, the
cauchy sequence has ∀ (n m : ℕ), n > N → m > N → |sₙ n - sₙ m| < 1. Now, the goal is to prove that
sₙ is bounded. Again, following Ross' proof of the theorem, the sequence sₙ, |sₙ n| ≤ |sₙ (N+1)|+ 1,
since there is finetely many terms before |sₙ (N+1)|+ 1 (or index ≤ N) which has a maximum. Then
choose M such that M is the maximum of |sₙ (N+1)|+ 1 and (|sₙ 0|, |sₙ 1| ... |sₙ N|), found by the
(Finset.range (N + 1)).sup' hnonempty (fun i => |sₙ i|), or the supremem of sₙ from index 0 - N.
After finding the maximum of these, this code proves that the sequence sₙ is bounded by that maximum
M. This has to be done in cases. If n > N then that means that |sₙ| is bounded by |sₙ (N+1)| + 1,
then le_max_of_le_right completes that |sₙ n| ≤ M. If n ≤ N then through hmem proves that n ≤ N
means n < N+1. Through Finset.le_sup', if n is in the set, then |sₙ n| is at most M_seq of all
values in that set. Then through le_max_of_le_left, if the value is ≤ the
left side of a max, it is ≤ the whole max. So |sₙ n| ≤ M. Thus in both cases |sₙ n| ≤ M and
a Cauchy sequence is bounded. This follows the proof technique from Ross' textbook.
-/

theorem cauchy_is_bounded (sₙ : ℕ → ℝ) :
  Is_Cauchy sₙ → Is_Bounded sₙ := by
  intro hcauchy
  have hε1 :
    ∃ N : ℕ, ∀ n m : ℕ, n > N → m > N → |sₙ n - sₙ m| < 1 := by
    have := hcauchy 1 (by exact Real.zero_lt_one)
    simpa using this
  rcases hε1 with ⟨N, hN⟩
  have hb : ∀ n > N, |sₙ n| ≤ |sₙ (N+ 1)| + 1 := by
    intro n hn
    have h := hN n (N +1)
    grind --allowed to use grind?
  have hnonempty : (Finset.range (N + 1)).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  let M_seq := (Finset.range (N + 1)).sup' hnonempty (fun i => |sₙ i|)
  let M := max M_seq (|sₙ (N+1)| + 1)
  have hbound : ∀ n : ℕ, |sₙ n| ≤ M := by
    intro n
    by_cases hn : n > N
    · have : |sₙ n| ≤ |sₙ (N+1)| + 1 := hb n hn
      exact le_max_of_le_right this
    · push Not at hn
      have hmem : n ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
      have : |sₙ n| ≤ M_seq :=
        Finset.le_sup' (fun i => |sₙ i|) hmem
      exact le_max_of_le_left this
  exact ⟨M, hbound⟩



/-
10.11 Theorem.
A sequence is a convergent sequence if and only if it is a Cauchy
sequence.
-/


theorem convergent_iff_cauchy (sₙ : ℕ → ℝ) :
  (∃ s : ℝ, Is_Convergent sₙ s) ↔ Is_Cauchy sₙ := by
    sorry
