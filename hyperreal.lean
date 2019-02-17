import data.real.basic
import order.filter

open filter

variable {f : ultrafilter ℕ}

def bigly_equal : setoid (ℕ → ℝ) := 
⟨ λ a b, {n : ℕ | a n = b n} ∈ f.val.sets,
  λ a, by simp only [eq_self_iff_true, (set.univ_def).symm, univ_sets], 
  λ a b ab, by simpa [eq_comm], 
  λ a b c ab bc, sets_of_superset f.val (inter_sets f.val ab bc) 
    (λ n (r : a n = b n ∧ b n = c n), eq.trans r.1 r.2)⟩

def hyperreal := quotient (@bigly_equal f)

notation `ℍ` := hyperreal

def seq.to_hyperreal : (ℕ → ℝ) → ℍ := @quotient.mk' (ℕ → ℝ) (@bigly_equal f)

def real.to_hyperreal : ℝ → ℍ := function.comp (@seq.to_hyperreal f) (λ x, (λ n, x))

instance seq_coe_hyperreal : has_coe (ℕ → ℝ) ℍ := ⟨@seq.to_hyperreal f⟩

instance real_coe_hyperreal : has_coe ℝ (@hyperreal f) := ⟨real.to_hyperreal⟩

theorem real.to_hyperreal_inj : function.injective (@real.to_hyperreal f) :=
begin
  intros r s rs, by_contra N,
  rw [real.to_hyperreal, seq.to_hyperreal, quotient.eq', bigly_equal] at rs, 
  simp only [N, set.set_of_false, empty_in_sets_eq_bot] at rs,
  apply (f.2).1 rs,
end

--def filter_univ_nat : filter ℕ := 
--⟨set.univ, trivial, λ x y a b, trivial, λ x y a b, trivial⟩

--instance real.to_hyperreal : has_coe ℝ (@hyperreal f) := ⟨λ x, (↑(λ n : ℕ, x) : ℍ)⟩