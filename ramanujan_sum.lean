-- THIS FILE IS WRONG, PLEASE SEE divergent_sums.lean

import data.real.basic
import tactic.linarith
import tactic.ring

local attribute [instance, priority 0] classical.prop_decidable

def seq : Type := ℕ → ℝ
def seq_smul (c : ℝ) : seq → seq := λ s n, c * (s n)
def seq_add : seq → seq → seq := λ s t n, s n + t n
def seq_shift (k : ℕ) : seq → seq := λ s n, s (n + k)
def seq_neg : seq → seq := λ s n, - s n
def seq_sub : seq → seq → seq := λ s t, seq_add s (seq_neg t)
notation s + t := seq_add s t
notation c * s := seq_smul c s
notation s % k := seq_shift k s
notation -s := seq_neg s
notation s - t := seq_sub s t

def fsum : seq → ℕ → ℝ := λ s n, finset.sum (finset.range (n + 1)) s
def has_gsum (s : seq) (r : ℝ) := ∀ ε > 0, ∃ N, ∀ x > N, abs (fsum s x - r) < ε

structure relational := (sequence : seq) (sum : ℝ)

constant R_summable : set relational
axiom functional (r1 r2 : relational) (hr1 : r1 ∈ R_summable) (hr2 : r2 ∈ R_summable) 
  : r1.sequence = r2.sequence → r1.sum = r2.sum
axiom extensionality (s : seq) (r : ℝ) : has_gsum s r → (⟨s, r⟩ : relational) ∈ R_summable
axiom linearity (r1 r2 : relational) (c : ℝ) (hr1 : r1 ∈ R_summable) (hr2 : r2 ∈ R_summable)
  : (⟨c * r1.sequence + r2.sequence, c * r1.sum + r2.sum⟩ : relational) ∈ R_summable
axiom stability (r : relational) (hr : r ∈ R_summable)
  : (⟨r.sequence % 1, r.sum - r.sequence 0⟩ : relational) ∈ R_summable

def zero_seq : seq := λ n, 0

lemma fsum_succ (s : seq) (n : ℕ) : fsum s (n + 1) = fsum s n + s (n + 1) :=
by unfold fsum; 
rw [finset.range_succ, finset.sum_insert (finset.not_mem_range_self), add_comm]

lemma shift_eval (s : seq) (k n : ℕ) : (s % n) k = s (k + n) := rfl
lemma shift_transit (s : seq) (m n : ℕ) : (s % m) % n = s % (m + n) :=
by unfold seq_shift; simp

lemma seq_add_zero (s : seq) : s + zero_seq = s :=
by unfold seq_add; unfold zero_seq; simp

lemma seq_zero_add (s : seq) : zero_seq + s = s :=
by unfold seq_add; unfold zero_seq; simp

lemma seq_one_mul (s : seq) : 1 * s = s :=
by unfold seq_smul; simp

lemma add_linearity (r1 r2 : relational) (hr1 : r1 ∈ R_summable) (hr2 : r2 ∈ R_summable)
  : (⟨r1.sequence + r2.sequence, r1.sum + r2.sum⟩ : relational) ∈ R_summable := 
by rw [←seq_one_mul r1.sequence, ←one_mul r1.sum]; apply linearity _ _ _ hr1 hr2

lemma fsum_zero_seq : ∀ x : ℕ, fsum zero_seq x = 0
| 0 := by {unfold fsum, unfold zero_seq, simp}
| (nat.succ x) := by rw [fsum_succ, fsum_zero_seq, zero_seq, zero_add]

lemma Rsum_zero_seq : (⟨zero_seq, 0⟩ : relational) ∈ R_summable :=
extensionality _ _ (λ ε hε, Exists.intro 0 (λ x hx, by rwa [sub_zero, fsum_zero_seq x, abs_zero]))

lemma smul_linearity (r : relational) (c : ℝ) (hr : r ∈ R_summable)
  : (⟨c * r.sequence, c * r.sum⟩ : relational) ∈ R_summable :=
begin
  have h1 : zero_seq = (⟨zero_seq, 0⟩ : relational).sequence := rfl,
  have h2 : 0 = (⟨zero_seq, 0⟩ : relational).sum := rfl,
  rw [←seq_add_zero (c * r.sequence), ←add_zero (c * r.sum), h1, h2], 
  apply linearity _ _ _ hr, rw [←h2], exact Rsum_zero_seq
end

lemma neg_linearity (r : relational) (hr : r ∈ R_summable)
  : (⟨-r.sequence, -r.sum⟩ : relational) ∈ R_summable :=
begin
  unfold seq_neg,
  conv {to_lhs, congr, funext, rw neg_eq_neg_one_mul, skip, rw neg_eq_neg_one_mul},
  apply smul_linearity _ _ hr,
end

lemma stability' (r : relational) (hr : r ∈ R_summable) (n : ℕ) (hn : n > 0)
  : (⟨r.sequence % n, r.sum - fsum r.sequence (n - 1)⟩ : relational) ∈ R_summable :=
begin
  induction n with k ih,
  { exfalso, apply not_lt_iff_eq_or_lt.mpr (or.inl rfl) hn },
  { by_cases h : k = 0,
    unfold fsum, 
    simp [h], apply stability _ hr,
    have ih' := ih (nat.pos_of_ne_zero h),
    have st_local := (shift_transit r.sequence k 1).symm,
    have se_local := shift_eval r.sequence 0 k,
    have sb_local := stability (⟨_, _⟩ : relational) ih',
    simp at ih' se_local st_local sb_local ⊢, clear ih,
    rw [←st_local, se_local, ←neg_add, add_comm (r.sequence k)] at sb_local,
    rw [←nat.sub_add_cancel (nat.pos_of_ne_zero h)] at sb_local {occs := occurrences.pos [3]},
    rwa [←fsum_succ, nat.sub_add_cancel (nat.pos_of_ne_zero h)] at sb_local,
  }
end

def alt_seq : ℕ → ℝ
| 0 := 1
| (nat.succ n) := - alt_seq n

def id_seq : ℕ → ℝ := λ n, (n + 1)
def alt_id_seq : ℕ → ℝ := λ n, alt_seq n * id_seq n

lemma alt_seq_zero : alt_seq 0 = 1 := rfl
lemma alt_seq_succ (n : ℕ) : alt_seq (n + 1) = - alt_seq n := rfl
lemma id_seq_zero : id_seq 0 = 1 := 
by unfold id_seq; rw [nat.cast_zero, zero_add]
lemma alt_id_seq_zero : alt_id_seq 0 = 1 :=
by unfold alt_id_seq; rw [alt_seq_zero, id_seq_zero, one_mul]

theorem Rsum_alt_seq : (⟨alt_seq, 1/2⟩ : relational) ∈ R_summable :=
begin
--never mind this is undecidable
end
