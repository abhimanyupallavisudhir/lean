import data.real.basic
import data.polynomial
import analysis.complex
import analysis.real
import analysis.exponential
import analysis.normed_space
import tactic.norm_num
import tactic.ring
import tactic.linarith

open filter real

-----<DELETE>

theorem pow_lt {x y : ℝ} {n : ℕ} (Hxy : x < y) (Hxpos : 0 < x) (Hnpos : 0 < n) : x ^ n < y ^ n :=
begin
  rw ←nat.sub_add_cancel Hnpos,
  induction (n - 1), { simpa only [pow_one] },
  rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
  apply mul_lt_mul ih (le_of_lt Hxy) Hxpos (le_of_lt (pow_pos (lt_trans Hxpos Hxy) _))
end

theorem pow_right_inj {x y : ℝ} {n : ℕ} (Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) (Hxyn : x ^ n = y ^ n) : x = y :=
begin
  rcases lt_trichotomy x y with hxy | rfl | hyx,
  { exact absurd Hxyn (ne_of_lt (pow_lt hxy Hxpos Hnpos)) },
  { refl },
  { exact absurd Hxyn (ne_of_gt (pow_lt hyx Hypos Hnpos)) },
end

noncomputable definition nth_root (x : ℝ) (n : ℕ) : ℝ := 
if x = 0 then 0 else exp ((log x) / n)

theorem exp_mul (x : ℝ) : ∀ n : ℕ, real.exp(n*x) = (real.exp(x))^n
| 0 := by rw [nat.cast_zero, zero_mul, real.exp_zero, pow_zero]
| (nat.succ n) := by rw [pow_succ', nat.cast_add_one, add_mul, real.exp_add, ←exp_mul, one_mul]

theorem nth_root_pos {x n} : x ≠ 0 → nth_root x n > 0 := by intro; simp [a, nth_root]; apply exp_pos

theorem nth_root_power {x : ℝ} {n} (Hxpos : 0 < x) (Hnpos : 0 < n): (nth_root x n) ^ n = x := 
begin
  simp [ne_of_gt Hxpos, nth_root],
  rw [←exp_mul, mul_div_cancel', exp_log Hxpos], 
  rw nat.cast_ne_zero, exact ne_of_gt Hnpos
end

theorem nth_root_unique {x y : ℝ} {n : ℕ}
(Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) (Hynx : y ^ n = x) : y = nth_root x n 
:= pow_right_inj Hypos (nth_root_pos (ne_of_gt Hxpos)) Hnpos (Hynx.trans (nth_root_power Hxpos Hnpos).symm)

-----</DELETE>


-----<MOVE>

theorem abs_pow (x : ℝ) : ∀ n : ℕ, abs(x ^ n) = (abs x) ^ n
| 0 := by simp
| (nat.succ n) := by rw [pow_succ, pow_succ, abs_mul, abs_pow]

theorem exp_lt_exp_iff (x y : ℝ) : x < y ↔ exp x < exp y :=
begin
  split,
  { exact exp_lt_exp },
  { intro,
    cases classical.em (x < y),
    { exact h },
    { exfalso,
      cases (eq_or_lt_of_le(le_of_not_lt h)) with hl he,
      { rw hl at a, apply ne_of_lt a rfl },
      { apply not_lt_of_gt a (exp_lt_exp he) } } }
end

theorem log_pos {x : ℝ} (hx : 1 < x) : log x > 0 :=
begin
  have hx' := hx, rw ←exp_log (lt_trans (by norm_num) hx') at hx,
  rwa [←exp_zero, ←exp_lt_exp_iff] at hx,
end

-----</MOVE>

def tendsto_punctured (f : ℝ → ℝ) (L : ℝ)
:= ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ≠ 0 → abs x < δ → abs (f x - L) < ε

private lemma tendsto_mul_zero_of_one (f : ℝ → ℝ) (g : ℝ → ℝ) (L0 : ℝ)
: tendsto f (nhds 0) (nhds 0) → tendsto_punctured g 1 → f 0 = 0 → g 0 = L0 → tendsto (f * g) (nhds 0) (nhds 0) :=
begin
  simp only [tendsto_nhds_of_metric, tendsto_punctured, dist, sub_zero, pi.mul_apply], 
  intros Hf Hg Hf0 Hg0 ε he, 
  cases (Hf (min (abs (ε/(1 + ε))) 1) (lt_min (abs_pos_of_ne_zero (div_ne_zero (ne_of_gt he) (ne_of_gt (add_pos (by norm_num) he)))) (by norm_num))) with δ_f Hf1, 
  cases (Hg (min ε 1) (lt_min he (by norm_num))) with δ_g Hg1,
  cases Hf1 with hd_f Hf2, cases Hg1 with hd_g Hg2, 
  existsi (min δ_f δ_g), existsi (lt_min hd_f hd_g),
  intros x hx, cases (lt_min_iff.mp hx) with hxf hxg,
  cases classical.em (x = 0) with xhole xpunc,
  { simpa [xhole, Hf0] },
  { have Hf3 := lt_min_iff.mp (Hf2 hxf),
    have Hg3 := lt_min_iff.mp (Hg2 x xpunc hxg),
    have Hg4 : abs (g x) < 1 + ε,
      have Hg4'1 := lt_sub_iff_add_lt'.mp ((abs_lt.mp (Hg3.1)).1),
      have Hg4'2 := sub_lt_iff_lt_add'.mp (abs_lt.mp (Hg3.1)).2,
      apply abs_lt.mpr, split;linarith,
    rw [abs_of_pos (div_pos he (add_pos (by norm_num : (1 : ℝ) > 0) he))] at Hf3,
    rw [abs_mul, ←@div_mul_cancel _ _ ε (1 + ε) (ne_of_gt (add_pos (by norm_num : (1 : ℝ) > 0) he))],
    apply mul_lt_mul' (le_of_lt (Hf3.1)) Hg4 (abs_nonneg _) (div_pos he (add_pos (by norm_num : (1 : ℝ) > 0) he)) }
end

lemma tendsto_mul_zero_of_nonzero (f : ℝ → ℝ) (g : ℝ → ℝ) (L0 : ℝ) (L : ℝ) (hL : L ≠ 0)
: tendsto f (nhds 0) (nhds 0) → tendsto_punctured g L → f 0 = 0 → g 0 = L0 → tendsto (f * g) (nhds 0) (nhds 0) :=
begin
  intros tf0 tgL f0 g0,
  change tendsto (λ x, f x * g x) (nhds 0) (nhds 0),
  conv { congr, funext, rw [←div_mul_cancel (g x) hL, ←mul_assoc] },
  rw [←zero_mul L] {occs := occurrences.pos [2]},
  apply tendsto_mul, {
    apply tendsto_mul_zero_of_one,
    { exact tf0 },
    { intros ε he, cases (tgL (abs(L) * ε) (mul_pos (abs_pos_iff.mpr hL) he)) with δ tgL1, cases tgL1 with hd tgL2,
      existsi δ, existsi hd, intros x hx hxd,
      have tgL3 := tgL2 x hx hxd,
      change abs (g x / L - 1) < ε,
      rwa [←mul_lt_mul_left (abs_pos_iff.mpr hL), ←abs_mul, mul_sub, mul_div_cancel' _ hL, mul_one] },
    { exact f0 },
    { rwa div_right_inj hL } },
  { exact tendsto_const_nhds }
end

lemma tendsto_mul_zero_of_zero (f : ℝ → ℝ) (g : ℝ → ℝ) (L : ℝ)
: tendsto f (nhds 0) (nhds 0) → tendsto_punctured g L → f 0 = 0 → g 0 = 0 → tendsto (f * g) (nhds 0) (nhds 0) :=
begin
  cases classical.em (L = 0),
  { rw h, intros tf0 tg0 f0 g0,
    rw [←zero_mul (0 : ℝ)] {occs := occurrences.pos [2]},
    apply tendsto_mul tf0,
    { simp [tendsto_nhds_of_metric, dist],
      intros ε he, cases (tg0 ε he) with δ tg1, cases tg1 with hd tg2,
      existsi δ, existsi hd, intros x hxd,
      have tg3 := tg2 x,
      cases classical.em (x = 0) with hx hx,
      { simpa [hx, g0] },
      { have tg4 := tg3 hx hxd, rwa sub_zero at tg4 } } },
  { apply tendsto_mul_zero_of_nonzero, exact h }
end

lemma tendsto_punctured_of_tendsto (f : ℝ → ℝ) (L : ℝ) : tendsto f (nhds 0) (nhds L) → tendsto_punctured f L :=
begin
  intro,
  simp only [tendsto_nhds_of_metric, dist, sub_zero, tendsto_punctured] at a ⊢,
  intros e he, have a' := a e he, cases a' with d a'', cases a'' with hd a''',
  existsi d, existsi hd, intros x hx, exact a''',
end

lemma tendsto_punctured_iff_tendsto (f : ℝ → ℝ) (L : ℝ)
: tendsto_punctured (λ h, (f h) / h) L ↔ tendsto (λ h, (f h - L * h) / h) (nhds 0) (nhds 0) :=
begin
  split,
  { simp only [tendsto_nhds_of_metric, dist, sub_zero],
    intros Htp ε Hε, have Htp1 := Htp ε Hε,
    cases Htp1 with δ Htp2, cases Htp2 with Hδ Htp3,
    existsi δ, existsi Hδ, intros h Hhd, have Htp4 := Htp3 h,
    cases classical.em (h = 0) with Hh0 Hh0, { simpa [Hh0] },
    rw [sub_div, mul_div_cancel _ Hh0], apply Htp4 Hh0 Hhd },
  { intros Ht ε Hε,
    simp only [tendsto_nhds_of_metric, dist, sub_zero] at Ht ⊢, have Ht1 := Ht ε Hε,
    cases Ht1 with δ Ht1, cases Ht1 with Hδ Ht2, existsi δ, existsi Hδ, 
    intros h Hh0 Hhd, have Ht3 := Ht2 Hhd,
    rwa [sub_div, mul_div_cancel _ Hh0] at Ht3 }
end

lemma tendsto_of_tendsto_punctured (f g : ℝ → ℝ) (L : ℝ) (Hg : g 0 = 0)
: tendsto_punctured (λ h, (f h) / (g h)) L → tendsto (λ h, (f h - L * (g h)) / (g h)) (nhds 0) (nhds 0) :=
begin
  simp only [tendsto_nhds_of_metric, dist, sub_zero],
  intros Htp ε Hε, have Htp1 := Htp ε Hε,
  cases Htp1 with δ Htp2, cases Htp2 with Hδ Htp3,
  existsi δ, existsi Hδ, intros h Hhd, have Htp4 := Htp3 h,
  cases classical.em (g h = 0) with Hg0 Hg0, { simpa [Hg0] },
  rw [sub_div, mul_div_cancel _ Hg0], apply Htp4 _ Hhd,
  intro Hh0, apply Hg0, rwa Hh0
end

lemma tendsto_punctured_comp {f g : ℝ → ℝ} {x : ℝ} 
: tendsto_punctured g 0 → tendsto_punctured f x → tendsto_punctured (f ∘ g) x := 
begin
  intros Hg Hf ε Hε,
  have Hf1 := Hf ε Hε, cases Hf1 with δ₁ Hf2, cases Hf2 with Hδ₁ Hf3,
  have Hg1 := Hg δ₁ Hδ₁, cases Hg1 with δ₂ Hg2, cases Hg2 with Hδ₂ Hg3,
  existsi (min δ₁ δ₂), existsi (lt_min Hδ₁ Hδ₂), intros h Hh0 Hhd, 
  have Hg4 := Hg3 h Hh0 (lt_min_iff.mp Hhd).2, have Hf4 := Hf3 (g h),
  simp at Hg4,
  cases classical.em (g h = 0) with p p,
  { rw [function.comp_app, p], sorry },
  { exact Hf4 p Hg4 }  
end

lemma tendsto_punctured_neg {f : ℝ → ℝ} {L : ℝ} : tendsto_punctured f L → tendsto_punctured (-f) (-L) :=
begin
  intros Hf ε Hε, have Hf1 := Hf ε Hε, cases Hf1 with δ Hf2, cases Hf2 with Hδ Hf3, existsi δ, existsi Hδ,
  intros x hole Hx, have Hf4 := Hf3 x hole Hx,
  rwa [pi.neg_apply, ←neg_neg (-f x - -L), neg_neg_sub_neg, abs_neg],
end

lemma tendsto_punctured_neg_iff (f : ℝ → ℝ) (L : ℝ) : tendsto_punctured f L ↔ tendsto_punctured (-f) (-L) :=
begin
  split, {apply tendsto_punctured_neg },
  intro temp, rw [←neg_neg f, ←neg_neg L],
  apply tendsto_punctured_neg temp,
end

private lemma tendsto_punctured_mul_of_pos_nonneg (f : ℝ → ℝ) (g : ℝ → ℝ) {Lf : ℝ} {Lg : ℝ} (hLf : Lf > 0) (hLg : Lg ≥ 0)
: tendsto_punctured f Lf → tendsto_punctured g Lg → tendsto_punctured (f * g) (Lf * Lg) :=
begin
  intros Hf Hg ε Hε, 
  have hLgf : Lg + Lf > 0 := add_pos_of_nonneg_of_pos hLg hLf,
  have h : Lg + Lf ≠ 0 := ne_of_gt hLgf,
  have Hf1 := Hf (min  (min ((ε / 4)/(abs (Lg + Lf))) ((sqrt ε) / 4)) (2 / 3))
    (lt_min (lt_min (div_pos (div_pos Hε (by norm_num))
    (abs_pos_of_ne_zero h)) (div_pos (sqrt_pos.mpr Hε) (by norm_num))) (by norm_num)),
  have Hg1 := Hg (min (min ((ε / 4)/(abs (Lg + Lf))) ((sqrt ε) / 4)) (2 / 3))
    (lt_min (lt_min (div_pos (div_pos Hε (by norm_num))
    (abs_pos_of_ne_zero h)) (div_pos (sqrt_pos.mpr Hε) (by norm_num))) (by norm_num)),
  cases Hf1 with δ₁ Hf2, cases Hf2 with Hδ₁ Hf3,
  cases Hg1 with δ₂ Hg2, cases Hg2 with Hδ₂ Hg3,
  existsi (min δ₁ δ₂), existsi lt_min Hδ₁ Hδ₂,
  intros x hole Hx, rw pi.mul_apply,
  have Hf4 := lt_min_iff.mp (Hf3 x hole (lt_min_iff.mp Hx).1), rw lt_min_iff at Hf4,
  have Hg4 := lt_min_iff.mp (Hg3 x hole (lt_min_iff.mp Hx).2), rw lt_min_iff at Hg4,
  have convertor : f x * g x - Lf * Lg = (f x - Lf) * Lg + (g x - Lg) * Lf + (f x - Lf) * (g x - Lg) := by ring,
  rw convertor,
  apply lt_of_le_of_lt (abs_add_three _ _ _ : 
                      _ ≤  abs ((f x - Lf) * Lg) + abs ((g x - Lg) * Lf) + abs((f x - Lf) * (g x - Lg))),
  rw [abs_mul, abs_mul, abs_mul],
  apply lt_of_le_of_lt ( _ : _ ≤ (ε / 4 / abs (Lg + Lf)) * abs Lg + abs (g x - Lg) * abs Lf + abs (f x - Lf) * abs (g x - Lg)),
  swap,
    rw [add_le_add_iff_right, add_le_add_iff_right],
    apply mul_le_mul_of_nonneg_right (le_of_lt Hf4.1.1) (abs_nonneg _),
  apply lt_of_le_of_lt ( _ : _ ≤ (ε / 4 / abs (Lg + Lf)) * abs Lg + (ε / 4 / abs (Lg + Lf)) * abs Lf + abs (f x - Lf) * abs (g x - Lg)),
  swap,
    rw [add_le_add_iff_right, add_le_add_iff_left],
    apply mul_le_mul_of_nonneg_right (le_of_lt Hg4.1.1) (abs_nonneg _),
  apply lt_of_le_of_lt (_ : _ ≤ ε / 4 / abs (Lg + Lf) * abs Lg + ε / 4 / abs (Lg + Lf) * abs Lf + ((sqrt ε) / 4) * ((sqrt ε) / 4)),
  swap,
    rw add_le_add_iff_left,
    apply mul_le_mul (le_of_lt Hf4.1.2) (le_of_lt Hg4.1.2) (abs_nonneg _) (le_of_lt (div_pos (sqrt_pos.mpr Hε) (by norm_num))),
  rw [←mul_add, ←pow_two, div_pow _ (by norm_num : (4 : ℝ) ≠ 0) _, sqr_sqrt (le_of_lt Hε), 
      abs_of_pos hLf, abs_of_nonneg hLg, abs_of_pos hLgf, div_mul_cancel _ h, 
      div_eq_mul_one_div, div_eq_mul_one_div ε _, ←mul_add, mul_lt_iff_lt_one_right Hε],
  norm_num
end

private lemma tendsto_punctured_mul_of_nonneg_nonneg (f : ℝ → ℝ) (g : ℝ → ℝ) {Lf : ℝ} {Lg : ℝ} (hLf : Lf ≥ 0) (hLg : Lg ≥ 0)
: tendsto_punctured f Lf → tendsto_punctured g Lg → tendsto_punctured (f * g) (Lf * Lg) :=
begin
  cases lt_or_eq_of_le hLf with hLf' hLf',
  { apply tendsto_punctured_mul_of_pos_nonneg _ _ hLf' hLg },
  cases lt_or_eq_of_le hLg with hLg' hLg',
  { intros hf hg, revert hg hf, rw [mul_comm, mul_comm Lf],
    apply tendsto_punctured_mul_of_pos_nonneg _ _ hLg' hLf },
  rw [←hLf', ←hLg', zero_mul],
  intros hf hg ε Hε,
  have hf1 := hf (sqrt ε) (sqrt_pos.mpr Hε), cases hf1 with δ₁ hf2, cases hf2 with Hδ₁ hf3,
  have hg1 := hg (sqrt ε) (sqrt_pos.mpr Hε), cases hg1 with δ₂ hg2, cases hg2 with Hδ₂ hg3,
  existsi (min δ₁ δ₂), existsi lt_min Hδ₁ Hδ₂, intros x hole hx,
  have hf4 := hf3 x hole (lt_min_iff.mp hx).1,
  have hg4 := hg3 x hole (lt_min_iff.mp hx).2,
  rw sub_zero at hf4 hg4 ⊢,
  rw [pi.mul_apply, abs_mul, ←sqrt_mul_self (le_of_lt Hε), sqrt_mul (le_of_lt Hε)],
  apply mul_lt_mul' (le_of_lt hf4) hg4 (abs_nonneg _) (sqrt_pos.mpr Hε)
end

lemma tendsto_punctured_mul (f : ℝ → ℝ) (g : ℝ → ℝ) (Lf : ℝ) (Lg : ℝ)
: tendsto_punctured f Lf → tendsto_punctured g Lg → tendsto_punctured (f * g) (Lf * Lg) :=
begin
  cases lt_or_ge Lf 0 with hLf hLf,
  { cases lt_or_ge Lg 0 with hLg hLg,
    { have hLf' := neg_nonneg_of_nonpos (le_of_lt hLf),
      have hLg' := neg_nonneg_of_nonpos (le_of_lt hLg),
      rw [tendsto_punctured_neg_iff f, tendsto_punctured_neg_iff g, ←neg_mul_neg, ←neg_mul_neg Lf],
      apply tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf' hLg' },
    { have hLf' := neg_nonneg_of_nonpos (le_of_lt hLf),
      rw [tendsto_punctured_neg_iff f, tendsto_punctured_neg_iff (f * g), neg_mul_eq_neg_mul, neg_mul_eq_neg_mul],
      apply tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf' hLg } },
  { cases lt_or_ge Lg 0 with hLg hLg,
    { have hLg' := neg_nonneg_of_nonpos (le_of_lt hLg),
      rw [tendsto_punctured_neg_iff g, tendsto_punctured_neg_iff (f * g), neg_mul_eq_mul_neg, neg_mul_eq_mul_neg],
      apply tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf hLg' },
    { exact tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf hLg } }
end

/-must be defined in this odd way because tendsto does not automatically
puncture the neighbourhood -- we use the fact that 0/0 = 0 in Lean-/
def has_derivative_at (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ) : Prop 
:= (tendsto (λ h, (f (x0 + h) - f (x0) - f'x0 * h)/h) (nhds 0) (nhds 0))

lemma has_derivative_at_iff_eps_del (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
: has_derivative_at f x0 f'x0 ↔
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, abs h < δ → abs ((f(x0 + h) - f(x0) - f'x0 * h) / h) < ε 
  := by simp [has_derivative_at, tendsto_nhds_of_metric, dist]

lemma has_derivative_at_iff_eps_del' (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
: has_derivative_at f x0 f'x0 ↔
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → abs h < δ → abs ((f(x0 + h) - f(x0))/h - f'x0) < ε :=
  begin
  rw has_derivative_at_iff_eps_del, split,
  { intros a ε Hε, have a1 := a ε Hε, cases a1 with δ a2, cases a2 with Hd a3,
    existsi δ, existsi Hd, intros h Hh, have a4 := a3 h, 
    rwa [sub_div, mul_div_cancel _ Hh ] at a4 },
  { intros a ε He, have a1 := a ε He, cases a1 with δ a2, cases a2 with Hd a3,
    existsi δ, existsi Hd, intro h, have a4 := a3 h, intro Hhd,
    cases classical.em (h ≠ 0) with N Y,
    { have a5 := a4 N Hhd, rwa [sub_div, mul_div_cancel _ N ] },
    { rw auto.not_not_eq at Y, simpa [Y] } }
  end

def has_derivative (f : ℝ → ℝ) (diffdom : set ℝ) (f' : ℝ → ℝ) 
:= ∀ x ∈ diffdom, has_derivative_at f x (f' x)

def has_derivative_everywhere (f : ℝ → ℝ) (f' : ℝ → ℝ) := ∀ x : ℝ, has_derivative_at f x (f' x)

def differentiable_at (f : ℝ → ℝ) (x : ℝ) := ∃ f'x, has_derivative_at f x f'x

def differentiable_at' (f : ℝ → ℝ) (x : ℝ) := ∃ f' : ℝ → ℝ, has_derivative_at f x (f' x)

def differentiable (f : ℝ → ℝ) (diffdom : set ℝ) := ∃ f', has_derivative f diffdom f'

def differentiable_everywhere (f : ℝ → ℝ) := ∃ f', has_derivative_everywhere f f'

lemma has_derivative_of_has_derivative_everywhere {f : ℝ → ℝ} {f' : ℝ → ℝ} {diffdom : set ℝ}
: has_derivative_everywhere f f' → has_derivative f diffdom f' := λ R x D, R x

lemma has_derivative_at_of_has_derivative (f : ℝ → ℝ) (x : ℝ) (diffdom : set ℝ) (f' : ℝ → ℝ) (Hx : x ∈ diffdom)
: has_derivative f diffdom f' → has_derivative_at f x (f' x) := λ a, a x Hx

lemma has_derivative_at_of_has_derivative_everywhere (f : ℝ → ℝ) (x : ℝ) (f' : ℝ → ℝ) 
: has_derivative_everywhere f f' → has_derivative_at f x (f' x) := λ a, a x

lemma derivative_everywhere_iff_univ (f : ℝ → ℝ) (f' : ℝ → ℝ) 
: has_derivative_everywhere f f' ↔ has_derivative f (set.univ) f' :=
begin
  split,
  { intros t x hx, apply has_derivative_at_of_has_derivative_everywhere f x f' t },
  { intros s x, apply s x true.intro }
end

lemma derivative_at_unique (f : ℝ → ℝ) (x : ℝ)
: ∀ (y₁ y₂ : ℝ), has_derivative_at f x y₁ → has_derivative_at f x y₂ → y₁ = y₂ :=
begin
  intros L1 L2 H1 H2, rw has_derivative_at_iff_eps_del' at H1 H2, by_contradiction,
  have H11 := H1 (abs((L1 - L2))/2) (half_pos(abs_pos_of_ne_zero (sub_ne_zero_of_ne a))),
  have H21 := H2 (abs((L1 - L2))/2) (half_pos(abs_pos_of_ne_zero (sub_ne_zero_of_ne a))),
  cases H11 with δ₁ H12, cases H12 with Hd1 H13, cases H21 with δ₂ H22, cases H22 with Hd2 H23,
  have D1 : abs (min δ₁ δ₂ / 2) < δ₁, 
    rw abs_of_pos (half_pos (lt_min Hd1 Hd2)), 
    apply lt_of_lt_of_le (half_lt_self(lt_min Hd1 Hd2)) (min_le_left δ₁ δ₂),
  have D2 : abs (min δ₁ δ₂ / 2) < δ₂, 
    rw abs_of_pos (half_pos (lt_min Hd1 Hd2)), 
    apply lt_of_lt_of_le (half_lt_self(lt_min Hd1 Hd2)) (min_le_right δ₁ δ₂),
  have H14 := H13 ((min δ₁ δ₂)/2) (ne_of_gt (half_pos (lt_min Hd1 Hd2))) D1,
  have H24 := H23 ((min δ₁ δ₂)/2) (ne_of_gt (half_pos (lt_min Hd1 Hd2))) D2,
  have H15 := abs_lt.mp H14, have H25 := abs_lt.mp H24,
  cases lt_or_gt_of_ne a with a1 a2,
  { rw ←sub_lt_zero at a1,
    have H16 := H15.2, have H26 := H25.1, clear H15 H25 H14 H24 H13 H23 H1 H2 a,
    rw [abs_of_neg a1, sub_lt_iff_lt_add', neg_div, sub_div L1, ←sub_eq_add_neg, ←sub_add, sub_half] at H16,
    rw [abs_of_neg a1, lt_sub_iff_add_lt, neg_div, neg_neg, sub_div L1, sub_add, half_sub, sub_neg_eq_add] at H26,
    revert H26, apply not_lt_of_gt H16 },
  { change L2 < L1 at a2, rw ←sub_pos at a2,
    have H16 := H15.1, have H26 := H25.2, clear H15 H25 H14 H24 H13 H23 H1 H2 a,
    rw [abs_of_pos a2, lt_sub_iff_add_lt, sub_div, ←sub_eq_neg_add, ←sub_add, sub_half] at H16,
    rw [abs_of_pos a2, sub_lt_iff_lt_add, sub_div L1, sub_add, half_sub, sub_neg_eq_add] at H26,
    revert H26, apply not_lt_of_gt H16 }
end

lemma derivative_at_exists_unique (f : ℝ → ℝ) (x : ℝ) (Hdiff : differentiable_at f x)
: (∃! f'x, has_derivative_at f x f'x) 
:= exists_unique_of_exists_of_unique Hdiff (derivative_at_unique f x)

lemma derivative_unique (f : ℝ → ℝ) (diffdom : set ℝ) 
: ∀ (f₁ f₂ : ℝ → ℝ), has_derivative f diffdom f₁ → has_derivative f diffdom f₂ → ∀ x ∈ diffdom, f₁ x = f₂ x 
:= λ f₁ f₂ H1 H2 x Hx, derivative_at_unique _ _ _ _ (H1 x Hx) (H2 x Hx)

lemma derivative_everywhere_unique (f : ℝ → ℝ)
: ∀ (f₁ f₂ : ℝ → ℝ), has_derivative_everywhere f f₁ → has_derivative_everywhere f f₂ → f₁ = f₂ 
:= λ f₁ f₂ H1 H2, funext (λ x, derivative_at_unique _ _ _ _ (H1 _) (H2 _))

lemma derivative_everywhere_exists_unique (f : ℝ → ℝ) (Hdiff : ∃ f', has_derivative_everywhere f f')
: ∃! f', has_derivative_everywhere f f' 
:= exists_unique_of_exists_of_unique Hdiff (derivative_everywhere_unique f)

-----DERIVATIVE PROPERTIES------

theorem limit_h_order : ∀ n : ℕ, n ≠ 0 → (tendsto (λ h : ℝ, h^n) (nhds 0) (nhds 0)) :=
begin
  intros n Hn, simp [tendsto_nhds_of_metric, dist],
  intros ε He, existsi (min (1/2 : ℝ) ( (nth_root ε n)/2)), 
  split, 
  { apply lt_min, norm_num, apply half_pos (nth_root_pos (ne_of_gt He)) },
  { intros x Hx, rw abs_pow,
    have Hx1 : abs x < 1, apply @lt_trans ℝ _ _ (1/2) _ (lt_min_iff.mp Hx).1, norm_num,
    have Hx2 : abs x < nth_root ε n := @lt_trans ℝ _ _ ((nth_root ε n)/2) _ (lt_min_iff.mp Hx).2 (half_lt_self (nth_root_pos (ne_of_gt He))),
    cases classical.em (x = 0), { rwa [h, abs_zero, zero_pow (nat.pos_of_ne_zero Hn) ] },
    { rw [←@nth_root_power _ n He (nat.pos_iff_ne_zero.mpr Hn)], 
      apply pow_lt Hx2 (abs_pos_iff.mpr h) (nat.pos_of_ne_zero Hn) } }
end

theorem continuity_of_differentiability_everywhere (f : ℝ → ℝ)
: differentiable_everywhere f → ∀ x : ℝ, tendsto (λ (h : ℝ), f (x + h) - f x) (nhds 0) (nhds 0) :=
begin
  intros hfd x, cases hfd with f' hfd,
  have lifesavingrewrite : (λ (h : ℝ), f (x + h) - f x) = (λ (h : ℝ), (h * ((f (x + h) - f x) / h))),
    funext, 
    cases classical.em (h = 0) with p p,
    { simp [p] },
    { rwa mul_div_cancel' },
  rw lifesavingrewrite,
  apply tendsto_mul_zero_of_zero,
  { apply tendsto_id },
  { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'], exact hfd x },
  { refl },
  { apply div_zero }
end

theorem derivative_constant_zero (c : ℝ) : has_derivative_everywhere (function.const _ c) 0 :=
begin
  rw function.const, intro x, rw has_derivative_at_iff_eps_del',
  intros ε He, existsi (1 : ℝ), split, norm_num,
  intros, simpa,
end

theorem derivative_add (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (diffdom : set ℝ)
: has_derivative f diffdom f' → has_derivative g diffdom g' → has_derivative (f + g) diffdom (f' + g') :=
begin 
  intros Hf Hg x indom, rw has_derivative_at,
  simp only [pi.add_apply, add_mul, sub_add_eq_sub_sub],
  have convertor : (λ (h : ℝ), (f (x + h) + g (x + h) - f x - g x - f' x * h - g' x * h) / h) 
                 = (λ (h : ℝ), ((f (x + h) - f x - f' x * h) / h + (g (x + h) - g x - g' x * h) / h)),
  { funext, ring },
  rw [←zero_add (0 : ℝ)] {occs := occurrences.pos [2]},
  rw convertor, apply tendsto_add (Hf _ indom) (Hg _ indom),
end

theorem derivative_everywhere_add (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) 
: has_derivative_everywhere f f' → has_derivative_everywhere g g' → has_derivative_everywhere (f + g) (f' + g') :=
begin 
  rw [derivative_everywhere_iff_univ, derivative_everywhere_iff_univ, derivative_everywhere_iff_univ], 
  apply derivative_add,
end

theorem derivative_everywhere_sum (s : finset ℕ) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ)
: (∀ a : ℕ, has_derivative_everywhere (f a) (f' a))
  → has_derivative_everywhere (λ x, finset.sum s (λ a, f a x)) (λ x, finset.sum s (λ a, f' a x)) := 
begin
  intro Df,
  apply finset.induction_on s,
  { simp, apply derivative_constant_zero },
  { intros b t bt Dfs,
    simp [finset.sum_insert bt] at Dfs ⊢,
    apply derivative_everywhere_add _ _ _ _ (Df b) Dfs }
end

theorem derivative_everywhere_mul (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ)
: has_derivative_everywhere f f' → has_derivative_everywhere g g' → has_derivative_everywhere (f * g) (f' * g + f * g') :=
begin
  intros Hf Hg x, rw has_derivative_at,
  simp only [pi.add_apply, pi.mul_apply, add_mul, sub_add_eq_sub_sub],
  have convertor : (λ (h : ℝ), (f (x + h) * g (x + h) - f x * g x - f' x * g x * h - f x * g' x * h) / h) = 
                   (λ (h : ℝ), g (x) * ((f (x + h) - f (x) - f' x * h) / h) + f (x) * ((g (x + h) - g (x) - g' x * h) / h) + ((f (x + h) - f (x)) * ((g (x + h) - g (x)) / h) )),
  { funext, ring },
  rw convertor, clear convertor,
  rw [←zero_add (0 : ℝ)] {occs := occurrences.pos [2]},
  apply tendsto_add,
  { rw [←zero_add (0 : ℝ)] {occs := occurrences.pos [2]},
    apply tendsto_add,
    { rw [←mul_zero ((g x) : ℝ)] {occs := occurrences.pos [2]},
      apply tendsto_mul, apply tendsto_const_nhds, apply Hf },
    { rw [←mul_zero ((f x) : ℝ)] {occs := occurrences.pos [2]},
      apply tendsto_mul, apply tendsto_const_nhds, apply Hg } },
  { apply tendsto_mul_zero_of_zero,
    { apply continuity_of_differentiability_everywhere,
      existsi f', exact Hf },
    { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'],
      exact Hg x },
    simp, simp }
end 

theorem derivative_everywhere_const_mul (c : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) 
: has_derivative_everywhere f f' → has_derivative_everywhere ((function.const _ c) * f) ((function.const _ c) * f') :=
begin
  intro hf,
  have g : has_derivative_everywhere (function.const ℝ c * f) ((function.const ℝ 0) * f + (function.const ℝ c * f'))
    := derivative_everywhere_mul _ _ _ _ (derivative_constant_zero _) hf,
  rwa [(by {funext, simp} : (function.const _ 0) * f = 0), zero_add] at g,
end

theorem derivative_everywhere_const_mul' (c : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ)
: has_derivative_everywhere f f' → has_derivative_everywhere (λ x, c * f x) (λ x, c * f' x) 
:= derivative_everywhere_const_mul _ _ _

lemma derivative_h_substitution (f f' g : ℝ → ℝ) (Hg : differentiable_everywhere g)
: has_derivative_everywhere f f' 
→ ∀ x : ℝ, tendsto_punctured (λ h, (f (g (x + h)) - f (g x)) / (g (x + h) - g x)) (f' (g x)) := 
begin
  intros Hf x,
  conv { congr, funext, rw [←add_sub_cancel'_right (g x) (g (x + h))] 
       { occs := occurrences.pos [1] } },
  change tendsto_punctured (((λ (H : ℝ), (f (g x + H) - f (g x)) / H)) ∘ (λ h, g (x + h) - g x)) (f' (g x)),
  apply tendsto_punctured_comp,
  { apply tendsto_punctured_of_tendsto _ _ (continuity_of_differentiability_everywhere _ Hg _) },
  { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'], apply Hf }
end

theorem chain_rule (f : ℝ → ℝ) (g : ℝ → ℝ) (f' : ℝ → ℝ) (g' : ℝ → ℝ)
: has_derivative_everywhere f f' → has_derivative_everywhere g g' 
→ has_derivative_everywhere (λ x, f (g x)) (λ x, f' (g x) * g' x) :=
begin
  intros Hf Hg x,
  have convertor : (λ h, (f (g (x + h)) - f (g x)) / h) 
                  = λ h, (((f (g (x + h)) - f (g x)) / (g (x + h) - g x)) * ((g (x + h) - g x) / h)),
    funext, cases classical.em (g (x + h) - g x = 0) with Hh Hh,
    { rw [Hh, zero_div, mul_zero, eq_of_sub_eq_zero Hh, sub_self, zero_div] },
    { rw [div_mul_div_cancel], intro H0, apply Hh, rw [H0, add_zero, sub_self], exact Hh },
  rw [has_derivative_at_iff_eps_del', ←tendsto_punctured, convertor],
  apply tendsto_punctured_mul,
  { apply derivative_h_substitution,
    existsi g', exact Hg, exact Hf },
  { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'], 
    apply has_derivative_at_of_has_derivative_everywhere _ _ _ Hg }                
end

--Chain rule, L' Hospital

-----TRIVIAL THEORMES-----
--mean value theorem, squeeze theorem, rolle's theorem, etc.

-----DERIVATIVE DATA-----

theorem derivative_id_one : has_derivative_everywhere id 1 :=
begin
  intro x, rw has_derivative_at_iff_eps_del',
  intros ε He, existsi (1 : ℝ), split, norm_num, 
  intros h ha hb, simp, rw [div_self ha], simpa,
end

theorem id_differentiable_everywhere : differentiable_everywhere id := exists.intro 1 derivative_id_one

theorem derivative_pow {n : ℕ} : has_derivative_everywhere (λ x, x ^ n) (λ x, n * x ^ (n - 1)) := 
begin 
  induction n with n h, { simp, apply derivative_constant_zero },
  have rw1 : (λ (x : ℝ), x ^ nat.succ n) = (λ (x : ℝ), x ^ n * x) := by { funext, rw pow_succ' },
  have rw2 : (λ (x : ℝ), ↑(nat.succ n) * x ^ (nat.succ n - 1)) = (λ (x : ℝ), (↑n * x ^ (n - 1)) * x + x ^ n * 1),
    funext,
    cases n, { simp },
    { rw [nat.succ_sub_one, mul_assoc, ←pow_succ', nat.sub_add_cancel (nat.succ_pos n), 
          nat.cast_succ, add_mul, one_mul, mul_one] },
  rw [rw1, rw2],
  apply derivative_everywhere_mul _ _ _ _ h (derivative_id_one)
end

theorem derivative_sq : has_derivative_everywhere (λ x, x ^ 2) (λ x, 2 * x) :=
begin
  rw (by simp : (λ (x : ℝ), 2 * x) = (λ (x : ℝ), ↑2 * x ^ (2 - 1))), 
  apply @derivative_pow 2,
end

theorem derivative_polynomial (p : polynomial ℝ) 
: has_derivative_everywhere (λ x, polynomial.eval x p) (λ x, polynomial.eval x (polynomial.derivative p)) :=
begin
  apply polynomial.induction_on p,
  { simp [polynomial.eval_C], exact derivative_constant_zero },
  { simp [polynomial.derivative_add, polynomial.eval_add],
    intros p1 q1 Dp1 Dq1,
    apply derivative_everywhere_add _ _ _ _ Dp1 Dq1 },
  { intros n a Dxn,
    simp [polynomial.eval_mul, polynomial.derivative_monomial, polynomial.eval_pow],
    rw [←nat.add_sub_cancel n 1] {occs := occurrences.pos [3]}, rw add_comm, simp only [mul_assoc],
    conv {congr, skip, rw [←nat.cast_one, ←nat.cast_add]},
    apply derivative_everywhere_const_mul _ _ _ derivative_pow }
end

theorem derivative_polynomial' (a : ℕ → ℝ) (N : ℕ) : has_derivative_everywhere 
(λ x : ℝ, finset.sum (finset.range N) (λ (k : ℕ), a k * x ^ k))
(λ x : ℝ, finset.sum (finset.range N) (λ (k : ℕ), k * a k * x ^ (k - 1))) :=
begin
  induction N with n ih,
  { simp, apply derivative_constant_zero },
  { simp,
    apply derivative_everywhere_add,
    { conv { congr, skip, funext, rw [mul_comm ↑n _, mul_assoc] },
      apply derivative_everywhere_const_mul',
      apply derivative_pow },
    { exact ih } }
end

/-
private lemma req_ineq3 (x : ℝ) : 0 ≤ exp x - 1 - x - x^2 / 2 := sorry
private lemma req_ineq2 (x : ℝ) : 0 ≤ exp x - 1 - x := sorry
private lemma req_ineq1 {x : ℝ} :  abs ((exp x - 1 - x) / x) ≤ abs (exp x - 1) := sorry

private lemma req_ineq1 {x : ℝ} (Hx : x > 0):  abs ((exp x - 1 - x) / x) ≤ abs (exp x - 1) := 
begin
  rcases lt_trichotomy x 0 with h | h | h,
  { sorry },
  { simp [h] },
  {
    have h1 : abs ((exp x - 1 - x) / x) = (exp x - 1 - x) / x := abs_of_nonneg (div_nonneg (req_ineq2 _) h),
    have h2 : abs (exp x - 1) = exp x - 1,
      rw ←exp_zero,
      apply abs_of_nonneg (sub_nonneg_of_le(exp_le_exp (le_of_lt h))),
    rw [h1, h2, sub_div, div_self(ne_of_gt h), sub_le_sub_iff_right],
    rcases lt_trichotomy x 1 with h' | h' | h',
    { apply le_trans (_ : _ ≤ x + 1),
      { rw [←le_sub_iff_add_le, ←sub_nonneg],
        exact (req_ineq2 x) },
      { apply div_le_of_le_mul h,
        rw [sub_le_iff_le_add', mul_add, add_comm],
      }
    },
    { simp [h'], norm_num },
    { apply le_trans (_ : _ ≤ exp x / x),
      { rw [div_eq_mul_one_div, mul_le_iff_le_one_right (exp_pos x), one_div_eq_inv],
        apply inv_le_one (le_of_lt h') },
      { rw [sub_div, sub_le_self_iff, one_div_eq_inv, inv_nonneg],
        apply le_of_lt h } } }
end

theorem derivative_exp : has_derivative_everywhere exp exp :=
begin
  intro,
  have convertor : ∀ h : ℝ, (exp (x + h) - exp x - exp x * h) / h = exp x * ((exp h - 1 - h)/h)
    := by { intro, simp [exp_add], ring },
  simp only [has_derivative_at, convertor],
  rw [←mul_zero ((exp x) : ℝ)] {occs := occurrences.pos [2]},
  apply tendsto_mul,
  { apply tendsto_const_nhds },
  { simp only [tendsto_nhds_of_metric, dist, sub_zero],
    intros,
    existsi (log(1 + ε)), existsi log_pos ((lt_add_iff_pos_right 1).mpr H),
    intros h Hh,
    apply lt_of_le_of_lt (_ : abs ((exp h - 1 - h) / h) ≤ abs(exp h - 1)),
    { cases abs_lt.mp Hh, apply abs_lt.mpr (and.intro _ _),
      { rw [exp_lt_exp_iff, exp_neg, exp_log (@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H)] at left,
        rw [←real.add_lt_add_iff_left 1, ←sub_eq_add_neg, add_sub_cancel'_right],
        apply lt_trans _ left,
        rw [←mul_lt_mul_left (@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H), inv_eq_one_div, 
            mul_one_div_cancel(ne_of_gt(@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H)),
            ←mul_self_sub_mul_self_eq, one_mul], 
        apply sub_lt_self _ (mul_self_pos (ne_of_gt H)) },
      { rwa [exp_lt_exp_iff, exp_log (@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H), 
             ←sub_lt_iff_lt_add'] at right } },
    { apply req_ineq1 } }
end

theorem derivative_exp' : has_derivative_everywhere exp exp :=
begin
  intro,
  have convertor : ∀ h : ℝ, (exp (x + h) - exp x - exp x * h) / h = exp x * ((exp h - 1 - h)/h)
    := by { intro, simp [exp_add], ring },
  simp only [has_derivative_at, convertor],
  rw [←mul_zero ((exp x) : ℝ)] {occs := occurrences.pos [2]},
  apply tendsto_mul,
  { apply tendsto_const_nhds },
  { simp only [tendsto_nhds_of_metric, dist, sub_zero],
    intros,
    existsi (min (2 * ε) (log(1 + ε))), 
    existsi lt_min (mul_pos (two_pos : (2 : ℝ) > 0) H) (log_pos ((lt_add_iff_pos_right 1).mpr H)),
    intros h Hh,
    rcases lt_trichotomy h 0 with hsgn | hsgn | hsgn,
    { have Hh' := (lt_min_iff.mp Hh).1, rw [abs_of_neg hsgn, mul_comm] at Hh',
      have Hh'' := div_lt_of_mul_lt_of_pos (two_pos) Hh',
      rw abs_of_nonpos (div_nonpos_of_nonneg_of_neg (req_ineq2 h) hsgn),
      apply lt_of_le_of_lt (_ : _ ≤ -h / 2) Hh'',
      rw [neg_div, neg_le_neg_iff],
      sorry
    },
    { simpa [hsgn] },
    { have Hh' := (lt_min_iff.mp Hh).2,
      apply lt_of_le_of_lt (_ : abs ((exp h - 1 - h) / h) ≤ abs(exp h - 1)),
      { cases abs_lt.mp Hh', apply abs_lt.mpr (and.intro _ _),
        { rw [exp_lt_exp_iff, exp_neg, exp_log (@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H)] at left,
          rw [←real.add_lt_add_iff_left 1, ←sub_eq_add_neg, add_sub_cancel'_right],
          apply lt_trans _ left,
          rw [←mul_lt_mul_left (@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H), inv_eq_one_div, 
              mul_one_div_cancel(ne_of_gt(@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H)),
              ←mul_self_sub_mul_self_eq, one_mul], 
          apply sub_lt_self _ (mul_self_pos (ne_of_gt H)) },
        { rwa [exp_lt_exp_iff, exp_log (@add_pos _ _ 1 ε (by norm_num : (0 : ℝ) < 1) H), 
              ←sub_lt_iff_lt_add'] at right } },
      { apply req_ineq1 hsgn } },
    }
end


theorem derivative_cau_seq {x : ℝ} {a : ℕ → ℝ} 
(Hf : is_cau_seq abs (λ (n : ℕ), finset.sum (finset.range n) (λ (k : ℕ), a k * x ^ k)))
: is_cau_seq abs (λ (n : ℕ), finset.sum (finset.range n) (λ (k : ℕ), ↑k * a k * x ^ (k - 1))) 
:= sorry

theorem derivative_cau_seq_lim {A : ℕ → ℝ → ℝ} {A' : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ} {diffdom : set ℝ}
(HAB : ∀ n : ℕ, has_derivative (A n) diffdom (A' n))
(HC_A : ∀ x : ℝ, x ∈ diffdom → is_cau_seq abs (λ (n : ℕ), A n x))
(HC_A' : ∀ x : ℝ, x ∈ diffdom → is_cau_seq abs (λ (n : ℕ), A' n x))
(Hf : ∀ x : ℝ, x ∈ diffdom → f x = cau_seq.lim ⟨(λ (n : ℕ), A n x), HC_A _ ‹x ∈ diffdom›⟩)
(Hf' : ∀ x : ℝ, x ∈ diffdom → f' x = cau_seq.lim ⟨(λ (n : ℕ), A' n x), HC_A' _ ‹x ∈ diffdom›⟩)
: has_derivative f diffdom f' := sorry

theorem derivative_power_series (a : ℕ → ℝ) (radius : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ)
(Ha : ∀ x : ℝ, -radius < x ∧ x < radius → is_cau_seq abs (λ (n : ℕ), finset.sum (finset.range n) (λ (k : ℕ), a k * x ^ k)))
(Hf : ∀ x : ℝ, -radius < x ∧ x < radius → f x = 
  cau_seq.lim (⟨(λ n, (finset.range n).sum (λ k, a k * x ^ k)), Ha x ‹-radius < x ∧ x < radius›⟩))
(Hf' : ∀ x : ℝ, -radius < x ∧ x < radius → f' x = 
  cau_seq.lim (⟨(λ n, (finset.range n).sum (λ k, k * a k * x ^ (k - 1))), derivative_cau_seq (Ha x ‹-radius < x ∧ x < radius›)⟩))
: has_derivative f ({x : ℝ | -radius < x ∧ x < radius }) f' 
:= derivative_cau_seq_lim (λ n : ℕ, has_derivative_of_has_derivative_everywhere (@derivative_polynomial' a n)) _ _ Hf Hf'
-/



-----DERIVATIVE OPERATOR-----

noncomputable def derivative_at (f : ℝ → ℝ) (x : ℝ) {Hdiff : ∃ f'x, has_derivative_at f x f'x} := classical.some Hdiff
noncomputable def derivative (f : ℝ → ℝ) {Hdiff : ∃ f', has_derivative_everywhere f f'} := classical.some Hdiff
