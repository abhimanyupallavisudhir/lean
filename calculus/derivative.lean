import .dependencies
import .tendsto_punctured
import .unfold_eps_del

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
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → abs h < δ → abs ((f(x0 + h) - f(x0))/h - f'x0) < ε :=
begin
  split,
  { intro a, rw has_derivative_at_iff_eps_del at a,
    unfold_eps_del_1 id id id a,
  }
end


end derivative
