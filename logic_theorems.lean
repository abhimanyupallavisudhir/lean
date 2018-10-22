--Since bananas are tasty, bananas are tasty or the Eiffel tower is in Florida.
--But bananas are not tasty, so the Eiffel tower must be in Florida.
theorem explosion (P : Prop) (Q : Prop) (HP : P) (HnP : ¬ P) : Q :=
begin
    have HPQ : P ∨ Q,
      left, exact HP,
    cases HPQ with HP HQ,
  --case 1
      exfalso,
      apply HnP,
      exact HP,
  --case 2
      exact HQ,
end

--Since bananas are not tasty, bananas are not tasty when the Eiffel tower is not in Florida.
--But bananas are tasty, so the Eiffel tower must be in Florida.
theorem explosion2 (P : Prop) (Q : Prop) : ¬ P → (P → Q) :=
    begin
        intro HnP,
        have HnQnP : ¬ Q → ¬ P, 
            intro HnQ, 
            exact HnP,
        clear HnP,
        --intro HP,
        cases classical.em Q with HQ HnQ,
        --case 1
            intro HP,
            exact HQ,
        --case 2
            intro HP,
            exfalso,
            revert HP,
            apply HnQnP,
            exact HnQ,
    end

--Double If
theorem deduction_theorem (P : Prop) (Q : Prop) : (P → (P → Q)) → (P → Q) :=
    begin
    intro HPPQ,
    intro HP,
    have HP' := HP,
    revert HP',
    apply HPPQ,
    exact HP,
    end