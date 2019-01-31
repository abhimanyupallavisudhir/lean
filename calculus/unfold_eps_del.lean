import analysis.normed_space
open lean tactic interactive.types expr
open interactive (parse)
open lean.parser (ident)

/-Unfold epsilon delta, zero hypotheses-/
theorem unfold_eps_del_0 (c L : ℝ) (f fδ : ℝ → ℝ) (Hfδ : ∀ ε > 0, fδ ε > 0)
: (∀ ε h : ℝ, ε > 0 → abs (h - c) < fδ ε → abs (f h - L) < ε) → ∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(f h - L) < ε :=
λ H ε Hε, ⟨fδ ε, ⟨Hfδ ε Hε, λ h, H ε h Hε⟩⟩ 

theorem unfold_eps_del_0' (c L : ℝ) (f fδ : ℝ → ℝ) (Hfδ : ∀ ε > 0, fδ ε > 0)
: (∀ ε h : ℝ, ε > 0 → h ≠ 0 → abs (h - c) < fδ ε → abs (f h - L) < ε) → ∀ ε > 0, ∃ δ > 0, ∀ h, h ≠ 0 → abs(h - c) < δ → abs(f h - L) < ε :=
λ H ε Hε, ⟨fδ ε, ⟨Hfδ ε Hε, λ h, H ε h Hε⟩⟩

/-Unfold epsilon delta, one hypothesis-/
theorem unfold_eps_del_1' (c L : ℝ)

/-
meta def unfold_eps_del_1 (fε fδ fx : ℝ → ℝ)
(p : parse ident) : tactic unit := do H1 ← get_local p,
`[try {simp only [filter.tendsto_nhds_of_metric, dist], rw sub_zero}],
`[try {simp only [filter.tendsto_punctured]}],
`[have H1':= %%H1],
`[try {simp only [filter.tendsto_nhds_of_metric, dist] at H1', rw sub_zero at H1'}],
`[try {simp only [filter.tendsto_punctured] at H1'}],
`[intros ε ε0],
`[have H11 := H1 (fε ε) _],
`[cases H11 with δ H12],
`[cases H12 with Hδ H13],
`[existsi (fδ δ)],
`[existsi _],
`[intros x xd],
`[try {intro x0}],
`[have H14 := H13 (fx x) _],
`[try {have H15 := H14 _}]

meta def unfold_eps_del_2 {P1 P2 : Prop} (fε : ℝ → ℝ) (fδ : ℝ → ℝ → ℝ) (fx : ℝ → ℝ)
(H1 : P1) (H2 : P2) : tactic unit := do
`[try {simp only [filter.tendsto_nhds_of_metric, dist], rw sub_zero}],
`[try {simp only [filter.tendsto_punctured]}],
`[try {simp only [filter.tendsto_nhds_of_metric, dist] at H1, rw sub_zero at H1}],
`[try {simp only [filter.tendsto_nhds_of_metric, dist] at H2, rw sub_zero at H2}],
`[try {simp only [filter.tendsto_punctured] at H1}],
`[try {simp only [filter.tendsto_punctured] at H2}],
`[intros ε ε0],
`[have H11 := H1 (fε ε) _],
`[have H21 := H2 (fε ε) _],
`[cases H11 with δ₁ H12],
`[cases H21 with δ₂ H22],
`[cases H12 with Hδ₁ H13],
`[cases H22 with Hδ₂ H23],
`[existsi (fδ δ₁ δ₂)],
`[existsi _],
`[intros x xd],
`[try {intro x0}],
`[have H14 := H13 (fx x) _],
`[have H24 := H23 (fx x) _],
`[try {have H15 := H14 _}],
`[try {have H25 := H24 _}]

#check resolve_name
-/