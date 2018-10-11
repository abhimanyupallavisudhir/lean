import tactic.norm_num
definition cong_mod_37 (a b : ℤ) := ∃ k : ℤ, 37 * k = a - b

theorem cong_mod_37_equiv_reln : equivalence cong_mod_37 :=
begin
  split,
    rw reflexive,
    intro x,
    rw cong_mod_37,
    rw sub_self,
    fapply exists.intro,
      exact 0,
    simp,
  split,
    rw symmetric,
    intros x y,
    intro HsXY,
    rw cong_mod_37,
    rw cong_mod_37 at HsXY,
    cases HsXY with n Hn,
    fapply exists.intro,
      exact -n,
    show 37 * -n = y - x,
    calc 37 * -n = -(37*n) : by rw ←neg_mul_eq_mul_neg
          ... = -(x - y) : by rw Hn
          ... = y - x : by rw neg_sub,
--split,  
    rw transitive,
    intros x y z,
    intro HtXY,
    intro HtYZ,
    rw cong_mod_37,
    rw cong_mod_37 at HtXY,
    rw cong_mod_37 at HtYZ,
    cases HtXY with n Hn,
    cases HtYZ with m Hm,
    fapply exists.intro,
      exact n + m,
    show 37 * (n + m) = x - z,
    calc 37 * (n + m) = 37 * n + 37 * m : by rw mul_add
                  ... = x - y + 37 * m : by rw Hn
                  ... = x - y + (y - z) : by rw Hm
                  ... = x - z : by simp,
end