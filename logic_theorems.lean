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