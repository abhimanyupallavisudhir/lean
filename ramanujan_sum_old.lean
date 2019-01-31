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

def fsum (n : ℕ) : seq → ℝ := λ s, finset.sum (finset.range (n + 1)) s

noncomputable def gsum : seq → ℝ := 
λ s, if H : ∃ L : ℝ, ∀ ε > 0, ∃ N, ∀ x > N, abs (s x - L) < ε
then classical.some H else 0

axiom Rsum : seq → ℝ
axiom extensionality (s : seq) : gsum s ≠ 0 → Rsum s = gsum s
axiom linearity (s t : seq) (c : ℝ) : Rsum (c * s + t) = c * Rsum s + Rsum t
axiom stability (s : seq) : Rsum s = s 0 + Rsum (s % 1)

def zero_seq : seq := λ n, 0

lemma fsum_succ (n : ℕ) (s : seq) : fsum (n + 1) s = fsum n s + s (n + 1) :=
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

lemma add_linearity (s t : seq) : Rsum (s + t) = Rsum s + Rsum t :=
by rw [←seq_one_mul s, linearity, one_mul, seq_one_mul]

lemma Rsum_zero_seq : Rsum zero_seq = 0 :=
by rw [←add_self_iff_eq_zero, ←add_linearity, seq_add_zero zero_seq]

lemma smul_linearity (s : seq) (c : ℝ) : Rsum (c * s) = c * Rsum (s) :=
by rw [←seq_add_zero (c * s), linearity, Rsum_zero_seq];
   rw [←add_zero (c * Rsum s)] {occs := occurrences.pos[2]}

lemma neg_linearity (s : seq) : Rsum (- s) = - Rsum s :=
begin
  unfold seq_neg, 
  conv {to_lhs, congr, funext, rw neg_eq_neg_one_mul},
  rw [neg_eq_neg_one_mul (Rsum s)],
  apply smul_linearity,
end

lemma stability' (s : seq) (n : ℕ) (hn : n > 0) 
: Rsum s = fsum (n - 1) s + Rsum (s % n) :=
begin
  induction n with n ih,
    exfalso, apply not_lt_iff_eq_or_lt.mpr (or.inl rfl) hn,
  by_cases h : n = 0,
    unfold fsum, simp [h], apply stability,
  have ih' := ih (nat.pos_of_ne_zero h),
  have st_local := (shift_transit s n 1).symm,
  have se_local := shift_eval s 0 n,
  simp [stability (s % n)] at ⊢ ih' se_local st_local,
  rw [nat.succ_eq_add_one, st_local, ←nat.sub_add_cancel (nat.pos_of_ne_zero h), 
    fsum_succ, nat.sub_add_cancel (nat.pos_of_ne_zero h), ih', se_local],
  simp
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

theorem Rsum_alt_seq : Rsum alt_seq = 1 / 2 :=
begin
  have h := stability alt_seq,
  have h1 : alt_seq % 1 = - alt_seq,
    funext n,
    have se_local := shift_eval alt_seq n 1, 
    simp at se_local, simp [se_local, seq_neg, alt_seq_succ],
  simp at h1, 
  simp [alt_seq_zero, h1, neg_linearity, eq_add_neg_iff_add_eq, 
        (two_mul _).symm] at h,
  apply eq_one_div_of_mul_eq_one h,
end

theorem Rsum_alt_id_seq : Rsum alt_id_seq = 1/4 := 
begin
  have h := stability alt_id_seq, simp [alt_id_seq_zero] at h,
  have hs : alt_id_seq + alt_id_seq % 1 = alt_seq % 1,
    funext,
    have se_local := shift_eval alt_id_seq n 1,
    have se_local' := shift_eval alt_seq n 1,
    simp at se_local se_local', 
    simp [seq_add], rw [se_local, se_local'], 
    simp [alt_id_seq, id_seq], 
    rw [alt_seq_succ, ←neg_mul_eq_neg_mul, ←sub_eq_add_neg, 
        ←mul_sub, ←mul_neg_one, add_sub_add_left_eq_sub, 
        nat.cast_add, ←sub_sub, sub_self, zero_sub, nat.cast_one],
  have s_local := stability alt_seq, simp [alt_seq_zero] at hs s_local,
  apply eq_of_mul_eq_mul_left_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0),
  rw [(by norm_num : (2 : ℝ) * (1 / 4) = 1 / 2), ←Rsum_alt_seq, two_mul],
  rw [h] {occs := occurrences.pos [2]},
  rw [←add_assoc, ←add_linearity, hs, s_local],
end

theorem Rsum_id_seq : Rsum id_seq = - (1 / 12) := 
begin
  sorry -- this is not possible, because it violates the axioms. 
        -- I should actually be able to prove there is no Ramanujan sum 
        -- (the way I've defined it) for id_seq
end