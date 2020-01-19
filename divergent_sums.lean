import data.real.basic linear_algebra.basis data.finset
open classical
open finset 

local attribute [instance, priority 0] prop_decidable

structure is_sum (Sum : (ℕ → ℝ) → ℝ → Prop) : Prop :=
(wd : ∀ {s S₁ S₂}, Sum s S₁ → Sum s S₂ → S₁ = S₂)
(sum_add : ∀ {s t S T}, Sum s S → Sum t T → Sum (λ n, s n + t n) (S + T))
(sum_smul : ∀ {s S} c, Sum s S → Sum (λ n, c * s n) (c * S))
(sum_shift : ∀ {s S}, Sum s S → Sum (λ n, s (n + 1)) (S - s 0))

def has_sum (s : ℕ → ℝ) (S : ℝ) := ∀ Sum, is_sum Sum → ∀ T, Sum s T → T = S

theorem sum_of_has_sum (s : ℕ → ℝ) (S : ℝ) (HS : has_sum s S) 
  (Sum : (ℕ → ℝ) → ℝ → Prop) (H : is_sum Sum) (T : ℝ) (HT : Sum s T) : 
  Sum s S := 
by rwa (HS Sum H T HT).symm 

theorem has_sum_alt : has_sum (λ n, (-1) ^ n) (1/2) :=
begin
  intros Sum HSum T HT,
  have H3 := HSum.sum_shift HT,
  have H2 := HSum.sum_smul (-1) HT,
  have H0 := HSum.wd H2 H3,
  change _ = T - 1 at H0,
  linarith,
end

theorem has_sum_alt_id : has_sum (λ n, (-1) ^ n * n) (-1/4) :=
begin
  intros Sum HSum T HT,
  have HC : ∀ n : ℕ, (-1 : ℝ) ^ (n + 1) * (n + 1 : ℕ) + (-1) ^ n * n = 
    (-1) * (-1) ^ n
  := λ n, by rw [pow_succ, nat.cast_add, mul_add, nat.cast_one, mul_one, add_comm, 
      ←add_assoc, neg_one_mul, neg_mul_eq_neg_mul_symm, add_neg_self, zero_add], 
  have H3 := HSum.sum_shift HT,
  have H1 := HSum.sum_add H3 HT,
  have H2 := HSum.sum_smul (-1) H1,
  simp only [nat.cast_zero, mul_zero, sub_zero, HC, neg_one_mul, neg_neg] at H2,
  have H4 := has_sum_alt Sum HSum _ H2,
  linarith,
end

def fib : ℕ → ℝ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1)

theorem has_sum_fib : has_sum fib (-1) :=
have HC : ∀ n, fib n + fib (n + 1) = fib (n + 2) := λ n, rfl,
begin
  intros S HSum T HT,
  have H3 := HSum.sum_shift HT,
  have H33 := HSum.sum_shift H3,
  have H1 := HSum.sum_add HT H3,
  have H0 := HSum.wd H1 H33, -- can use linearity instead of wd
  simp only [fib, sub_zero] at H0,
  linarith,
end

-- if a sequence has two has_sums, everything is its sum 
-- (this is the case of not being summable, e.g. 1+1+1+...)
theorem has_sum_unique (s : ℕ → ℝ) (S₁ S₂ : ℝ) (H : S₁ ≠ S₂) : 
  has_sum s S₁ → has_sum s S₂ → ∀ S', has_sum s S' :=
λ HS₁ HS₂ T₁ Sum HSum T₂ HT₂, false.elim $ H $ HS₂ Sum HSum S₁ $ 
  sum_of_has_sum s S₁ HS₁ Sum HSum T₂ HT₂

open submodule

-- a sum operator that is "forced" to give a the sum s
-- a valid sum operator iff the shifts of a are linearly independent
-- in which case a can have any sum, and thus has_sum nothing
def forced_sum (s : ℕ → ℝ) (H : linear_independent ℝ (λ m n : ℕ, s (n + m))) (S : ℝ) : 
  (ℕ → ℝ) → ℝ → Prop :=
λ t T, ∃ Ht : t ∈ span ℝ (set.range (λ m n : ℕ, s (n + m))),
T = finsupp.sum (linear_independent.repr H ⟨t, Ht⟩)
  (λ n r, r * (S - (finset.range n).sum s))

-- linear algebra lemma
lemma spanning_set_subset_span 
  {R M : Type} [ring R] [add_comm_group M] [module R M] {s : set M} :
  s ⊆ span R s := 
span_le.mp (le_refl _)

-- finsupp lemma
lemma finsupp.mul_sum' 
  {α : Type} {β : Type} {γ : Type} [_inst_1 : semiring β] [_inst_2 : semiring γ] 
  (b : γ) (s : α →₀ β) {f : α → β → γ} (Hf0 : ∀ a, f a 0 = 0) 
  (Hfa : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) : 
  b * finsupp.sum s f = finsupp.sum s (λ (a : α) (c : β), b * f a c) := 
begin
  apply finsupp.induction s,
  { rw [finsupp.sum_zero_index, finsupp.sum_zero_index, mul_zero] },
  intros A B t Ht HB IH,
  rw [finsupp.sum_add_index Hf0 _, finsupp.sum_add_index _ _, mul_add, IH, 
    finsupp.sum_single_index, finsupp.sum_single_index],
  rw [Hf0, mul_zero],
  exact Hf0 _,
  exact λ a, by rw [Hf0, mul_zero],
  intros a b₁ b₂, rw [Hfa, mul_add],
  exact Hfa
end

-- finsupp lemma (another one)
lemma function_finsupp_sum (a : ℕ →₀ ℝ) (f : ℕ → ℕ → ℝ → ℝ) (k : ℕ) 
  (H0 : ∀ a b, f a b 0 = 0) (Hl : ∀ a b c₁ c₂, f a b (c₁ + c₂) = f a b c₁ + f a b c₂) : 
  (finsupp.sum a (λ m am, (λ n, f n m am))) k = finsupp.sum a (λ m am, f k m am) :=
begin
  apply finsupp.induction a,
  { simp only [finsupp.sum_zero_index], refl },
  intros t v a ht hv H,
  rw [finsupp.sum_add_index, finsupp.sum_add_index, 
    finsupp.sum_single_index, finsupp.sum_single_index],  
  { show f k t v + _ = f k t v + _, rw H },
  { exact H0 _ _ },
  { funext, apply H0 },
  { exact λ r, H0 _ _ },
  { exact Hl _ },
  { exact λ t, funext (λ x, by rw H0; refl) },
  { exact λ a b₁ b₂, funext (λ x, Hl _ _ _ _) }
end

-- show that forced_sum_actually does what we want
lemma forced_sum_val (s : ℕ → ℝ) (S : ℝ) 
  (H : linear_independent ℝ (λ m n : ℕ, s (n + m))) : 
  forced_sum s H S s S :=
begin
  have Hs₁ : s ∈ set.range (λ m n : ℕ, s (n + m)) := set.mem_range.mpr ⟨0, rfl⟩,
  have Hs₂ : s ∈ span ℝ (set.range (λ m n : ℕ, s (n + m))) := 
    spanning_set_subset_span Hs₁,
  have Hs₃ : (linear_independent.repr H) ⟨s, Hs₂⟩ = finsupp.single 0 1 := 
    linear_independent.repr_eq_single H 0 ⟨s, Hs₂⟩ rfl, 
  use Hs₂, simp [Hs₃, finsupp.sum_single_index],
end

-- forced_sum is a sum: some lemmas for the hard part
noncomputable def shift_repr 
  (s t : ℕ → ℝ) (Ht : t ∈ span ℝ ((λ (m n : ℕ), s (n + m)) '' set.univ)) :
  ℕ →₀ ℝ :=
have trep : _ := (finsupp.mem_span_iff_total ℝ).mp Ht,
finsupp.map_domain (λ x, x + 1) (classical.some trep)

def shift_repr_prop 
  (s t : ℕ → ℝ) (Ht : t ∈ span ℝ ((λ (m n : ℕ), s (n + m)) '' set.univ)) :
  finsupp.sum (shift_repr s t Ht) (λ (m : ℕ) (am : ℝ) (n : ℕ), am * s (n + m)) = 
  λ (n : ℕ), t (n + 1) :=
have trep : _ := (finsupp.mem_span_iff_total ℝ).mp Ht,
let a : _ := classical.some trep in
let b : _ := shift_repr s t Ht in
have Ha : finsupp.sum a (λ (m : ℕ) (am : ℝ) (n : ℕ), am * s (n + m)) = t := 
  classical.some_spec (classical.some_spec trep),
begin
  have Hn : ∀ n, (finsupp.sum a (λ (m : ℕ) (am : ℝ) (n : ℕ), am * s (n + m))) n = 
    t n
  := by rw Ha; exact λ n, rfl,
  have Hn' : ∀ (n : ℕ), finsupp.sum a (λ (m : ℕ) (am : ℝ), am * s (n + m)) = t n,
    intro n,
    rw [←(function_finsupp_sum a _ n _ _), Ha],
    exact λ m n, zero_mul _,
    exact λ m n q r, add_mul _ _ _,
  have Hb : ∀ n, finsupp.sum b (λ m bm, bm * s (n + m)) = 
    finsupp.sum a (λ m am, am * s (n + 1 + m))
  := by 
    { intro n, 
      convert @finsupp.sum_map_domain_index ℕ ℝ _ ℕ _ _ (λ x, x + 1) a _ _ _, 
      exact funext (λ m, funext (λ am, by rw [add_assoc, add_comm 1 m])),
      exact λ a, zero_mul _,
      exact λ n r s, add_mul _ _ _ },
  have YAY := λ n, Hn' (n + 1),    
  have YAY' : 
    ∀ (n : ℕ), finsupp.sum b (λ (m : ℕ) (am : ℝ), am * s (n + m)) = t (n + 1) 
  := λ n, by rw [Hb, YAY],
  have YAY'' : (λ n, finsupp.sum b (λ (m : ℕ) (am : ℝ), am * s (n + m))) = 
    (λ n, t (n + 1))
  := funext (λ n, YAY' n),
  have primr : (λ n, finsupp.sum b (λ m am, am * s (n + m))) = 
    (finsupp.sum b (λ m am n, am * s (n + m)))
  := by 
  { apply funext, intro n, apply (function_finsupp_sum b _ n _ _).symm,
    exact λ m n, zero_mul _,
    exact λ m n q r, add_mul _ _ _ },
  rw primr at YAY'',
  exact YAY'',
end

lemma shift_mem_span_shifts 
  (s t : ℕ → ℝ) (Ht : t ∈ span ℝ (set.range (λ (m n : ℕ), s (n + m)))) :
  (λ n, t (n + 1)) ∈ span ℝ (set.range (λ (m n : ℕ), s (n + m))) :=
begin
  rw set.image_univ.symm at Ht ⊢,
  let b := shift_repr s t Ht,
  have Hb := shift_repr_prop s t Ht,
  exact (finsupp.mem_span_iff_total _).mpr 
    ⟨b, ⟨(by rw finsupp.supported_univ; exact submodule.mem_top), by rw ←Hb; refl⟩⟩,
end

lemma forced_sum_shift 
  (s : ℕ → ℝ) (S : ℝ) (H : linear_independent ℝ (λ m n : ℕ, s (n + m))) : 
  ∀ {t T}, (forced_sum s H S) t T → (forced_sum s H S) (λ n, t (n + 1)) (T - t 0) :=
λ t T ⟨Ht, HT⟩, 
begin
  use shift_mem_span_shifts s t Ht,

end

-- forced_sum is a sum
lemma is_sum_forced_sum (s : ℕ → ℝ) (S : ℝ) 
  (H : linear_independent ℝ (λ m n : ℕ, s (n + m))) :
  is_sum (forced_sum s H S) :=
⟨ λ t T₁ T₂ ⟨Ht₁, HT₁⟩ ⟨Ht₂, HT₂⟩, by rw [HT₁, HT₂],
  λ t₁ t₂ T₁ T₂ ⟨Ht₁, HT₁⟩ ⟨Ht₂, HT₂⟩, 
  begin 
    use add_mem _ Ht₁ Ht₂,
    change _ = finsupp.sum ((linear_independent.repr H) ⟨t₁ + t₂, _⟩) _,
    have Hadd 
    : (linear_independent.repr H) ⟨t₁ + t₂, _⟩ = 
      (linear_independent.repr H) _ + (linear_independent.repr H) _ 
    := (linear_independent.repr H).add ⟨t₁, Ht₁⟩ ⟨t₂, Ht₂⟩, 
    rw [Hadd, HT₁, HT₂, ←finsupp.sum_add_index],
    { intro a, apply zero_mul },
    { intros a b c, apply add_mul }
  end,
  λ t T c ⟨Ht, HT⟩, 
  begin 
    use smul_mem _ c Ht,
    have Hsmul 
    : (linear_independent.repr H) ⟨λ n, c * t n, _⟩  = 
      c • (linear_independent.repr H) _ 
    := (linear_independent.repr H).smul c ⟨t, Ht⟩,
    rw [Hsmul, finsupp.sum_smul_index], simp only [mul_assoc],
    rw [←finsupp.mul_sum', HT],
    exact λ i, (zero_mul _),
    exact λ a b c, add_mul _ _ _,
    exact λ i, (zero_mul _)
  end,
  -- we've already done the hard part
  λ t T, forced_sum_shift s S H ⟩

theorem no_sum_of_lin_ind_shifts 
  (s : ℕ → ℝ) (H : linear_independent ℝ (λ m n : ℕ, s (n + m))) : 
  ∀ S : ℝ, ¬ has_sum s S :=
λ S HS, 
have X : _ := HS (forced_sum s H (S + 1)) (is_sum_forced_sum s (S + 1) H) (S + 1) 
  (forced_sum_val s (S + 1) H),
by linarith

-- CHALLENGE: formalise the proof here:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/
-- topic/Axiomatised.20summations/near/178884724
-- REQUIRES GENERATING FUNCTIONS, TAYLOR SERIES -- not currently in Lean!
theorem inv_shifts_lin_ind : linear_independent ℝ (λ m n : ℕ, 1 / (n + m + 1)) :=
begin

end
