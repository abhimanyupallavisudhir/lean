import analysis.normed_space
open lean tactic interactive.types expr
open interactive (parse)
open lean.parser (ident)

/-Unfold epsilon delta, zero hypotheses-/
theorem unfold_eps_del_0 (c L : ℝ) (f fδ : ℝ → ℝ) (Hfδ : ∀ ε > 0, fδ ε > 0)
: (∀ ε h : ℝ, ε > 0 → abs (h - c) < fδ ε → abs (f h - L) < ε) → ∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(f h - L) < ε :=
λ H ε Hε, ⟨fδ ε, ⟨Hfδ ε Hε, λ h, H ε h Hε⟩⟩ 

theorem unfold_eps_del_0' (c L : ℝ) (f fδ : ℝ → ℝ) (Hfδ : ∀ ε > 0, fδ ε > 0)
: (∀ ε h : ℝ, ε > 0 → h ≠ 0 → abs (h - c) < fδ ε → abs (f h - L) < ε) → ∀ ε > 0, ∃ δ > 0, ∀ h ≠ 0, abs(h - c) < δ → abs(f h - L) < ε :=
λ H ε Hε, ⟨fδ ε, ⟨Hfδ ε Hε, λ h, H ε h Hε⟩⟩

/-Unfold epsilon delta, one hypothesis-/
theorem unfold_eps_del_1 (c L : ℝ) (f g fε fδ fh : ℝ → ℝ) (Hfε : ∀ ε > 0, fε ε > 0) (Hfδ : ∀ δ > 0, fδ δ > 0) (Hfh : ∀ h δ, δ > 0 → abs (h - c) < fδ δ → abs (fh h - c) < δ)
: (∀ ε δ h : ℝ, ε > 0 → δ > 0 → abs (h - c) < fδ δ → abs (g (fh h) - L) < fε ε → abs (f h - L) < ε) 
→ ((∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(g h - L) < ε) 
    → (∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(f h - L) < ε)) :=
λ H Hf ε Hε, begin
  rcases (Hf (fε ε) (Hfε ε Hε)) with ⟨δ, ⟨Hδ, Hf3⟩⟩,
  exact ⟨fδ δ, ⟨Hfδ δ Hδ, λ h hd, H ε δ h Hε Hδ hd (Hf3 (fh h) (Hfh h δ Hδ hd))⟩⟩,
end

theorem unfold_eps_del_1' (c L : ℝ) (f g fε fδ fh : ℝ → ℝ) (Hfε : ∀ ε > 0, fε ε > 0) (Hfδ : ∀ δ > 0, fδ δ > 0) (Hfh : ∀ h δ, h ≠ 0 → δ > 0 → abs (h - c) < fδ δ → abs (fh h - c) < δ) (Hfh2 : ∀ h ≠ 0, fh h ≠ 0)
: (∀ ε δ h : ℝ, ε > 0 → δ > 0 → h ≠ 0 → abs (h - c) < fδ δ → abs (g (fh h) - L) < fε ε → abs (f h - L) < ε) 
→ ((∀ ε > 0, ∃ δ > 0, ∀ h ≠ 0, abs(h - c) < δ → abs(g h - L) < ε) 
    → (∀ ε > 0, ∃ δ > 0, ∀ h ≠ 0, abs(h - c) < δ → abs(f h - L) < ε)) :=
λ H Hf ε Hε, begin
  rcases (Hf (fε ε) (Hfε ε Hε)) with ⟨δ, ⟨Hδ, Hf3⟩⟩,
  exact ⟨fδ δ, ⟨Hfδ δ Hδ, λ h hd1 hd2, H ε δ h Hε Hδ hd1 hd2 (Hf3 (fh h) (Hfh2 h hd1) (Hfh h δ hd1 Hδ hd2))⟩⟩,
end

/-Unfold epsilon delta, two hypotheses-/
theorem unfold_eps_del_2 (c L : ℝ) (f g e fε₁ fε₂ fh₁ fh₂ : ℝ → ℝ) (fδ : ℝ → ℝ → ℝ) (Hfε₁ : ∀ ε > 0, fε₁ ε > 0) (Hfε₂ : ∀ ε > 0, fε₂ ε > 0) (Hfδ : ∀ δ₁ δ₂ > 0, fδ δ₁ δ₂ > 0) (Hfh₁2 : ∀ h δ₁ δ₂, δ₁ > 0 → δ₂ > 0 → abs (h - c) < fδ δ₁ δ₂ → abs (fh₁ h - c) < δ₁) (Hfh₂2 : ∀ h δ₁ δ₂, δ₁ > 0 → δ₂ > 0 → abs (h - c) < fδ δ₁ δ₂ → abs (fh₂ h - c) < δ₂)
: (∀ ε δ₁ δ₂ h : ℝ, ε > 0 → δ₁ > 0 → δ₂ > 0 → abs (h - c) < fδ δ₁ δ₂ → abs (g (fh₁ h) - L) < fε₁ ε → abs (e (fh₂ h) - L) < fε₂ ε → abs (f h - L) < ε)
→ ((∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(g h - L) < ε) 
   → (∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(e h - L) < ε) 
      → (∀ ε > 0, ∃ δ > 0, ∀ h, abs(h - c) < δ → abs(f h - L) < ε)) :=
λ H Hg He ε Hε, begin
  rcases (Hg (fε₁ ε) (Hfε₁ ε Hε)) with ⟨δ₁, ⟨Hδ₁, Hg3⟩⟩,
  rcases (He (fε₂ ε) (Hfε₂ ε Hε)) with ⟨δ₂, ⟨Hδ₂, He3⟩⟩,
  exact ⟨fδ δ₁ δ₂, ⟨Hfδ δ₁ δ₂ Hδ₁ Hδ₂, λ h hd, H ε δ₁ δ₂ h Hε Hδ₁ Hδ₂ hd (Hg3 (fh₁ h) (Hfh₁2 h δ₁ δ₂ Hδ₁ Hδ₂ hd)) (He3 (fh₂ h) (Hfh₂2 h δ₁ δ₂ Hδ₁ Hδ₂ hd))⟩⟩ 
end

theorem unfold_eps_del_2' (c L : ℝ) (f g e fε₁ fε₂ fh₁ fh₂ : ℝ → ℝ) (fδ : ℝ → ℝ → ℝ) (Hfε₁ : ∀ ε > 0, fε₁ ε > 0) (Hfε₂ : ∀ ε > 0, fε₂ ε > 0) (Hfδ : ∀ δ₁ δ₂ > 0, fδ δ₁ δ₂ > 0) (Hfh₁1 : ∀ h ≠ 0, fh₁ h ≠ 0) (Hfh₂1 : ∀ h ≠ 0, fh₂ h ≠ 0) (Hfh₁2 : ∀ h δ₁ δ₂, h ≠ 0 → δ₁ > 0 → δ₂ > 0 → abs (h - c) < fδ δ₁ δ₂ → abs (fh₁ h - c) < δ₁) (Hfh₂2 : ∀ h δ₁ δ₂, h ≠ 0 → δ₁ > 0 → δ₂ > 0 → abs (h - c) < fδ δ₁ δ₂ → abs (fh₂ h - c) < δ₂)
: (∀ ε δ₁ δ₂ h : ℝ, ε > 0 → δ₁ > 0 → δ₂ > 0 → h ≠ 0 → abs (h - c) < fδ δ₁ δ₂ → abs (g (fh₁ h) - L) < fε₁ ε → abs (e (fh₂ h) - L) < fε₂ ε → abs (f h - L) < ε)
→ ((∀ ε > 0, ∃ δ > 0, ∀ h ≠ 0, abs(h - c) < δ → abs(g h - L) < ε) 
   → (∀ ε > 0, ∃ δ > 0, ∀ h ≠ 0, abs(h - c) < δ → abs(e h - L) < ε) 
      → (∀ ε > 0, ∃ δ > 0, ∀ h ≠ 0, abs(h - c) < δ → abs(f h - L) < ε)) :=
λ H Hg He ε Hε, begin
  rcases (Hg (fε₁ ε) (Hfε₁ ε Hε)) with ⟨δ₁, ⟨Hδ₁, Hg3⟩⟩,
  rcases (He (fε₂ ε) (Hfε₂ ε Hε)) with ⟨δ₂, ⟨Hδ₂, He3⟩⟩,
  exact ⟨fδ δ₁ δ₂, ⟨Hfδ δ₁ δ₂ Hδ₁ Hδ₂, λ h hd1 hd2, H ε δ₁ δ₂ h Hε Hδ₁ Hδ₂ hd1 hd2 (Hg3 (fh₁ h) (Hfh₁1 h hd1) (Hfh₁2 h δ₁ δ₂ hd1 Hδ₁ Hδ₂ hd2)) (He3 (fh₂ h) (Hfh₂1 h hd1) (Hfh₂2 h δ₁ δ₂ hd1 Hδ₁ Hδ₂ hd2))⟩⟩ 
end