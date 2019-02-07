import .dependencies

open filter

section derivative

def has_derivative_at (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
:= (tendsto (λ h, (f (x0 + h) - f (x0) - f'x0 * h)/h) (nhds 0) (nhds 0))

lemma has_derivative_at_iff_eps_del (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
: has_derivative_at f x0 f'x0 ↔
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, abs h < δ → abs ((f(x0 + h) - f(x0) - f'x0 * h) / h) < ε 
  := by simp [has_derivative_at, tendsto_nhds_of_metric, dist]

lemma has_derivative_at_iff_eps_del' (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
: has_derivative_at f x0 f'x0 ↔
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → abs h < δ → abs ((f(x0 + h) - f(x0)) / h - f'x0) < ε :=
begin
  rw has_derivative_at_iff_eps_del, split,
  { intros a ε Hε, rcases (a ε Hε) with ⟨δ, ⟨Hd, a3⟩⟩,
    exact ⟨δ, ⟨Hd, λ h Hh, by have a4 := a3 h;
      rwa [sub_div, mul_div_cancel _ Hh ] at a4⟩⟩,
  { intros a ε He, rcases (a ε Hε) with ⟨δ, ⟨Hd, a3⟩⟩,
    refine ⟨δ, ⟨Hd, λ h, _⟩⟩, intro Hhd,
    by_cases Y : h ≠ 0,
    { have a5 := (a3 h) Y Hhd, rwa [sub_div, mul_div_cancel _ Y ] },
    { rw auto.not_not_eq at Y, simpa [Y] } },
end


end derivative
