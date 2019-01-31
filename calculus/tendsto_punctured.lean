import .dependencies
import .unfold_eps_del
import analysis.normed_space

open filter

def tendsto_punctured (f : ℝ → ℝ) (c L : ℝ)
:= ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - c) < δ → x - c ≠ 0 → abs (f x - L) < ε

lemma tendsto_punctured_scale (f : ℝ → ℝ) (c L k : ℝ)
: ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - c) < δ → x - c ≠ 0 → abs (f x - L) < k * ε := 
begin

end

--variables {α : Type} [topological_space α] (a : α)
--def nhds_punctured (a : α) : filter α 
--:= (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s ∧ s ≠ {a}}, principal s)
