---what's with rw mul_self_iff_eq_one? can't it be used to prove 0 = 1?

----QUESTION 1
import tactic.norm_num

theorem onea : ((∀ x : int, x^2 - 3*x + 2 = 0 → x = 1) → false) :=
begin
  intro HP,
  have H2 := HP 2,
  revert H2,
  norm_num,
end

theorem oneb : (∀ x : int, x = 1 → x^2 - 3*x + 2 = 0) :=
begin
  intro x,
  intro H1,
  rw H1,
  norm_num,
end

theorem onec : ((∀ x : int, x = 1 ↔  x^2 - 3*x + 2 = 0) → false) :=
begin
  intro HPQ,
  have H2 := HPQ 2,
  cases H2 with H2Q H2P,
  revert H2P,
  norm_num,  
end

lemma lm1 : ∀x : int, x - 1 = 0 ∨ x - 2 = 0 → x = 1 ∨ x = 2 :=
begin
  intro x,
  intro HT,
  cases HT with HT1 HT2,
  left,
  rw ←sub_eq_zero,
  exact HT1,
  right,
  rw ←sub_eq_zero,
  exact HT2,
end

lemma lm2 : ∀x : int, x^2 - 3*x + 2 = 0 → (x - 1)*(x - 2) = 0 := 
begin
  intro x,
  intro h,
  show (x - 1)*(x - 2) = 0, by
    calc
      (x - 1) * (x - 2)  = x * (x - 2) - 1 * (x - 2) : sub_mul x 1 (x-2)
                      ... = x*x - x*2 - 1*(x - 2) : by rw mul_sub x x 2
                      ... = x*x - x*2 - (1*x - 1 * 2) : by rw mul_sub 1 x 2
                      ... = x*x - x*2 - 1*x + 1 * 2 : by rw ←sub_add (x*x-x*2) (1*x) (1*2)
                      ... = x*x - x*2 - 1*x + 2 : by norm_num --why doesn't rw one_mul work??
                      ... = x*x - 2*x - 1*x + 2 : by rw mul_comm 2 x
                      ... = x*x - (2*x + 1*x) + 2 : by rw sub_sub (x*x) (2*x) (1*x)
                      ... = x*x - (2 + 1)*x + 2 : by rw ←add_mul 2 1 x
                      ... = x*x - 3*x + 2 : by norm_num
                      ... = x^2 - 3*x + 2 : by rw ←pow_two x
                      ... = 0 : by rw h
end

theorem oned : ∀x : int,  x^2 - 3*x + 2 = 0 ↔ x = 1 ∨ x = 2 :=
begin
  intro x,
  split,
  intro HX,
  apply lm1,
  rw ←mul_eq_zero,
  apply lm2,
  exact HX,
  intro HY,
  cases HY with HY1 HY2,
  rw HY1,
  norm_num,
  rw HY2,
  norm_num,
end

theorem onee : ∀x : int,  x^2 - 3*x + 2 = 0 → x = 1 ∨ x = 2 ∨ x = 3 :=
begin 
  intro x,
  intro HX,
  rw ←or_assoc,
  left,
  apply lm1,
  rw ←mul_eq_zero,
  show (x - 1) * (x - 2) = 0, by
    calc
      (x - 1) * (x - 2)  = x * (x - 2) - 1 * (x - 2) : sub_mul x 1 (x-2)
                     ... = x*x - x*2 - 1*(x - 2) : by rw mul_sub x x 2
                     ... = x*x - x*2 - (1*x - 1 * 2) : by rw mul_sub 1 x 2
                     ... = x*x - x*2 - 1*x + 1 * 2 : by rw ←sub_add (x*x-x*2) (1*x) (1*2)
                     ... = x*x - x*2 - 1*x + 2 : by norm_num --why doesn't rw one_mul work??
                     ... = x*x - 2*x - 1*x + 2 : by rw mul_comm 2 x
                     ... = x*x - (2*x + 1*x) + 2 : by rw sub_sub (x*x) (2*x) (1*x)
                     ... = x*x - (2 + 1)*x + 2 : by rw ←add_mul 2 1 x
                     ... = x*x - 3*x + 2 : by norm_num
                     ... = x^2 - 3*x + 2 : by rw ←pow_two x
                     ... = 0 : by rw HX
end

theorem onef : (∀x : int, x = 1 ∨ x = 2 ∨ x = 3 → x ^ 2 - 3 * x + 2 = 0) → false :=
begin 
  intro HX,
  have HX3 := HX 3,
  revert HX3,
  norm_num,
end

--QUESTION 2
theorem inheritance (P Q R: Prop) (HQP: Q → P) (HnQnR: ¬Q → ¬R) : R → P :=
begin
  intro HR,
  apply HQP,
  cases (classical.em Q) with HQ HnQ,
  exact HQ,
  exfalso,
  apply HnQnR,
  exact HnQ,
  exact HR,
end

--QUESTION 3
theorem infalso (P Q R S : Prop) (HP: P) (HnQ: ¬ Q) (HnR: ¬ R) (HS: S) 
(HX: (R → S) → (P → Q)) : false :=
begin
  apply HnQ,
  apply HX,
  intro HR,
  exfalso,
  apply HnR,
  exact HR,
  exact HP,
end

--QUESTION 4
--As an example consider:
---- P: Bob wins the election
---- Q: Bob is a good guy
---- R: All the voters are bad guys
----
----Then indeed: 
---- P -> (Q or R)      (If Bob has won the election, he must be a good guy, unless all the voters are bad guys.)
---- -Q -> (R or -P)    (If Bob is a bad guy, then he loses the election unless all the voters are bad guys.)
---- (Q and R) -> -P    (If Bob is a good guy, but the voters are all bad guys, he loses the election.)
----
----Observe that these statements are true regardless of whether Bob is a good guy or a bad guy, whether the voters are good or bad, or whether or not he wins the election.

theorem bob : 
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → P) := 
begin
  intro HXp,
  have HXpf := HXp false true true,
  apply HXpf,
  split,
  intro Hf,
  exfalso,
  exact Hf,
  split,
  intro Hf,
  exfalso,
  exact Hf trivial,
  intro Htt,
  cases Htt with Ht1 Ht2,
  intro Hf,
  exact Hf,
end

theorem bobagain : 
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → Q) := 
begin
  intro HXq,
  have HXqf := HXq true false true,
  apply HXqf,
  split,
  intro Ht,
  right,
  exact Ht,
  split,
  intro Hnf,
  left,
  trivial,
  intro Hft,
  intro Ht,
  cases Hft with Hf Ht,
  exact Hf,
end

theorem thereturnofbob : 
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → R) := 
begin
  intro HXr,
  have HXrf := HXr true true false,
  apply HXrf,
  split,
  intro Ht,
  left,
  exact Ht,
  split,
  intro Hnt,
  right,
  exact Hnt,
  intro Htf,
  cases Htf with Ht Hf,
  intro Ht,
  exact Hf,
end

----You can prove that the premises do not prove ¬P, ¬Q, ¬R in essentially the same way.
----That's left as an exercise to the reader. But note that the theorems above "essentially" proved them anyway, you can just copy-paste them and change the goal.

