import data.real.basic data.nat.prime data.real.irrational data.padics.padic_norm
import tactic.norm_num tactic.ring
local attribute [instance] nat.decidable_prime_1

------------------------------------------------
----------------TRIVIAL STARTERS----------------
------------------------------------------------

def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
def even (x : ℕ) := ∃ r : nat, 2 * r = x
def odd (x : ℕ) := ∃ r : nat, 2 * r + 1 = x

lemma zero_even_or_odd : (even 0) ∨ (odd 0) :=
  begin
    left,
      rw even,
      fapply exists.intro,
      exact 0,
      simp,    
  end

lemma de_morgan (P : nat → Prop) : (∀x : nat, ¬ P x) → (∃x : nat, P x) → false :=
    begin
        intro Hallnot,
        intro Hexiyes,
        cases Hexiyes with x Hx,
        have Hnx := Hallnot x,
        apply Hnx,
        exact Hx,
    end

lemma one_not_even : (even 1) → false :=
    begin
        intro H1e,
        rw even at H1e,
        revert H1e,
        apply de_morgan,
        intro x,
        intro H1e,
        have Hnx0 : x ≠ 0,
            cases classical.em (x = 0) with Hx0 Hnx0,
              --case Hx0
                  exfalso,
                  have H10 : 1 = 0,
                      show 1 = 0,
                      calc 1 = 1 : by refl
                         ... = 2 * x : by rw H1e
                         ... = 2 * 0 : by rw Hx0
                         ... = 0 : by norm_num,
                  revert H10,
                  exact dec_trivial,
              --case Hnx0
                  exact Hnx0,
        have Hnx1 : x ≠ 1,
            cases classical.em (x = 1) with Hx1 Hnx1,
              --case Hx1
                  exfalso,
                  have H12 : 1 = 2,
                      show 1 = 2,
                      calc 1 = 1 : by refl
                         ... = 2 * x : by rw H1e
                         ... = 2 * 1 : by rw Hx1
                         ... = 2 : by norm_num,
                  revert H12,
                  exact dec_trivial,
              --case Hnx0
                  exact Hnx1,
        have H2xg0l2 : 2 * x > 0 ∧ 2 * x < 2,
            split,
              rw H1e,
              norm_num,
          --split,
              rw H1e,
              norm_num,
        have Hxg0l1 : x > 0 ∧ x < 1,
            cases H2xg0l2 with H2xg0 H2xl2,
            split,
              rw nat.pos_iff_ne_zero, exact Hnx0,
          --split,
              cases classical.em (x < 1) with Hxl1 Hnxl1,
              --case Hxl1
                  exact Hxl1,
              --case Hnxl1
                  exfalso,
                  have Hxl1g1 : x < 1 ∨ x > 1,
                    apply lt_or_gt_of_ne,
                    exact Hnx1,
                  cases Hxl1g1 with Hxl1 Hxg1,
                  --case Hxl1
                      apply Hnxl1, exact Hxl1,
                  --case Hxg1
                      have H2xg2 : 2 * x > 2,
                        have Hxge0 : x ≥ 0,
                          apply ge_trans,
                          show x ≥ 1,
                            apply le_of_lt,
                            exact Hxg1,
                          exact dec_trivial,
                        rw mul_comm,
                        change x * 2 > 2 * 1, change 2 * 1 < x * 2,
                        rw mul_comm,
                        apply mul_lt_mul,
                        exact Hxg1,
                        exact dec_trivial,
                        exact dec_trivial,
                        exact Hxge0,
                      have Hn2xg2 : ¬ (2 * x > 2),
                        apply lt_asymm,
                        exact H2xl2,
                      apply Hn2xg2, 
                      exact H2xg2,
        clear H2xg0l2 H1e,
        cases Hxg0l1 with Hxg0 Hxl1,
        revert x Hxl1,
        exact dec_trivial,
    end

lemma nat_even_or_odd : ∀x : ℕ,  (even x) ∨ (odd x)
    | (0)       := zero_even_or_odd
    | (x + 1)   := 
        begin
            cases (nat_even_or_odd x) with Hxe Hxo,
            --case Hxe
                right,
                rw odd,
                rw even at Hxe,
                cases Hxe with r Hr,
                fapply exists.intro,
                    exact r,
                rw Hr,
            --case Hxo
                left,
                rw even,
                rw odd at Hxo,
                cases Hxo with r Hr,
                fapply exists.intro,
                    exact r + 1,
                show 2 * (r + 1) = x + 1,
                calc 2 * (r + 1) = 2 * r + 2 * 1 : by rw mul_add
                            ... = 2 * r + (1 + 1) : by norm_num
                            ... = 2 * r + 1 + 1 : by rw ←add_assoc
                            ... = x + 1 : by rw Hr
        end

lemma nat_even_xor_odd : ∀x : ℕ, ((even x) ∧ (odd x) → false) :=
    begin
        intro x,
        intro Hxexo,
        cases Hxexo with Hxe Hxo,
        rw even at Hxe,
        rw odd at Hxo,
        cases Hxe with r Hr,
        cases Hxo with s Hs,
        have Hrs : 2 * (r - s) = 1,
            calc 2 * (r - s) = 2 * (r - s) : by refl
                        ... = 2 * r - 2 * s : by rw nat.mul_sub_left_distrib
                        ... = 2 * r + 1 - (2 * s + 1) : by rw nat.add_sub_add_right
                        ... = x + 1 - (2 * s + 1) : by rw Hr
                        ... = x + 1 - x : by rw Hs
                        ... = 1 + x - x : by rw add_comm
                        ... = 1 : by rw nat.add_sub_cancel,
        clear Hr Hs,
        have H1e : even 1,
            fapply exists.intro,
            exact (r - s), exact Hrs,
        revert H1e,
        exact one_not_even,
    end

------------------------------------------------
-------------------APPETISERS-------------------
------------------------------------------------

theorem num_even_if_num_sq_even (x : ℕ) : (even (x ^ 2) → even x) :=
    begin
        cases (nat_even_or_odd x) with Hxe Hxo,
        --case Hxe
            intro Hx2e,
            exact Hxe,
        --case Hxo
            intro Hx2e,
            exfalso,
            rw odd at Hxo,
            rw even at Hx2e,
            cases Hxo with s Hs,
            cases Hx2e with r Hr,
            rw ←Hs at Hr,
            apply one_not_even, rw even,
            clear Hs, --just remove if you want, nobody cares
            fapply exists.intro, exact (r - 2 * s ^ 2 - 2 * s),
            ring at Hr, rw add_mul at Hr,
            rw @nat.pow_two s, rw ←mul_assoc, rw nat.mul_sub_left_distrib, rw nat.mul_sub_left_distrib, rw mul_assoc, rw ←mul_assoc, norm_num, rw ←mul_assoc, rw ←mul_assoc, norm_num, rw nat.sub_sub, rw ←add_right_inj (4 * s * s + 4 * s), rw nat.sub_add_cancel, rw ←add_assoc, rw add_comm, rw add_comm 1 (4 * s * s), rw ←add_assoc, rw add_comm (4 * s) (4 *s * s),
            exact Hr,
            --we introduced a new goal in that mess above because of subtraction in ℕ
            rw Hr, apply le_add_right, rw le_iff_eq_or_lt, left, refl,
    end