import data.real.basic
--Since bananas are tasty, bananas are tasty or the Eiffel tower is in Florida.
--But bananas are not tasty, so the Eiffel tower must be in Florida.
example (P : Prop) (Q : Prop) (HP : P) (HnP : ¬ P) : Q :=
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

theorem explosion (P : Prop) (Q : Prop) (HP : P) (HnP : ¬ P) : Q :=
    have hpq : P ∨ Q := or.intro_left Q HP,
    or.elim (hpq) (false.elim (HnP HP)) (λ hq, hq)

--Since bananas are not tasty, bananas are not tasty when they are not alien zombies.
--But bananas are tasty, so they must be alien zombies.
example (P : Prop) (Q : Prop) : ¬ P → (P → Q) :=
    begin
        intros HnP HP,
        have HnQnP : ¬ Q → ¬ P := λ HnQ, HnP,
        clear HnP,
        cases classical.em Q with HQ HnQ,
        --case 1
            exact HQ,
        --case 2
            exfalso,
            apply HnQnP HnQ HP,
    end

theorem explosion2 (P : Prop) (Q : Prop) : ¬ P → (P → Q) :=
    λ hnp hp, have hnqnp : ¬ Q → ¬ P := λ hnq, hnp,
    or.elim(classical.em Q) (λ hq, hq) (λ hnq, false.elim(hnqnp hnq hp))

--Double If
example (P : Prop) (Q : Prop) : (P → (P → Q)) → (P → Q) := by { intros HPPQ HP, apply HPPQ HP HP }
theorem deduction_theorem (P : Prop) (Q : Prop) : (P → (P → Q)) → (P → Q) := λ ppq p, ppq p p

--Barber paradox
variables ( men : Type ) ( barber : men )
variable ( shave : men →  men → Prop )
local infix ` shaves `:1000 := shave

example ( H :  ∀ him : men, barber shaves him ↔ ¬ him shaves him ) : false :=
    begin
        cases H barber, 
        have hby : shave barber barber, apply mpr, intro, apply mp; exact a,
        apply mp hby hby,
    end

theorem barber_is_dead ( H :  ∀ him : men, barber shaves him ↔ ¬ him shaves him ) :  false  :=
    iff.dcases_on(H barber) (λ mp mpr, mp (mpr (λ a, mp a a)) (mpr (λ a, mp a a)))

--Liar paradox
theorem pants_on_fire : ¬ ∃ P : Prop, P ↔ ¬P :=
begin
  intro HP, cases HP with P HP, cases HP with HPnP HnPP,
  cases classical.em P,
  { apply HPnP h h },
  { apply h (HnPP h) },
end

theorem pants_on_fire' : ¬ ∃ P : Prop, P ↔ ¬P :=
  (λ HP, Exists.dcases_on HP
    (λ P HP, iff.dcases_on HP
      (λ HPnP HnPP,
        or.dcases_on 
          (classical.em P) 
          (λ h, HPnP h h) 
          (λ h, h (HnPP h)))))

--Let's be constructive
theorem thisisok (P : Prop) : ¬(¬P ∧ ¬¬P) := λ a, a.2 a.1

theorem thisisuseful (P : Prop) : (¬P ∧ ¬¬P) ↔ ¬(P ∨ ¬P) := 
begin
  split,
  { intros a b,
    cases a with a1 a2,
    cases b; { apply a2 a1 } },
  { intro a, split,
    { intro b, apply a, left, exact b },
    { intro b, apply a, right, exact b } }
end

theorem thisisok' (P : Prop) : ¬¬(P ∨ ¬P) :=
begin
  rw ←thisisuseful, exact thisisok P,
end

open function
theorem invertible_of_bijective {α β : Type} (f : α → β) : bijective f → ∃ g : β → α, (g ∘ f = id ∧ f ∘ g = id) :=
begin
  intro bijjala,
  cases bijjala with injjala surjjala, rw injective at injjala, rw surjective at surjjala,
  let g : β → α := λ b, classical.some (surjjala b),
  existsi g, split,
  { funext, apply eq.symm(@injjala x (g (f x)) _), simp [g],
    rw eq_comm, apply classical.some_spec (surjjala (f x)) },
  { funext, simp [g],
    apply classical.some_spec (surjjala x) }
end

/---The blue-eyed islanders puzzle
structure tribal (day : ℕ) := mk ::
(eye : bool)    -- brown = ff, blue = tt
(state : bool)  -- island = tt, afterlife = ff
(knows : bool)  -- no = ff, yes = tt

axiom consistency (day1 : ℕ) (day2 : ℕ) (victim_t1 : tribal day1) (victim_t2 : tribal day2)  : 
    victim_t1.eye = victim_t2.eye
axiom death (today : ℕ) (victim : tribal today) (victim_tom : tribal (nat.succ(today))) : 
    victim.knows = tt → victim_tom.state = ff
axiom life (today : ℕ) (victim : tribal today) (victim_tom : tribal (nat.succ(today))) : 
    victim.knows = ff → victim_tom.state = tt-/

--misc tests
def tfae (props : list Prop)
:= ∀ i j : ℕ, i < props.length → j < props.length → (props.nth_le i (by assumption) → props.nth_le j (by assumption))


--def tfae_induction (props : list Prop) (HP : ∀ i : ℕ, i < props.length - 1 → props.nth_le i (begin apply lt_of_lt_of_le a nat.sub_one_le end) )


/-DOESN'T work, because le on nat and le on int are two different things-/
/-I guess the idea is that almost every property one can define of a type
  is defined within the framework of the type, and it doesn't make sense
  to compare such a property between types.

  But surely N = R should still be decidable? using cardinalities?
  -/

def F (T : Type) [has_le T] := ∃ o : T, ∀ i, i ≥ o
lemma FN : F ℕ := Exists.intro 0 nat.zero_le
lemma FZ : ¬ F ℤ :=
begin
  intro FZ,
  cases FZ with o Ho,
  have Ho' := Ho (o - 1),
  apply not_le_of_gt _ Ho', 
  rw [←sub_add_cancel o 1] {occs := occurrences.pos [1]},
  apply lt_add_of_pos_right _ (zero_lt_one),
end

theorem nat_ne_int : ℕ ≠ ℤ :=
begin
  intro,
  have H : F ℕ → F ℤ, sorry,
  apply FZ (H FN),
end

theorem natle_ne_intle : (⟨ℕ, (≤)⟩ : Σ α : Type, α → α → Prop) ≠ ⟨ℤ, (≤)⟩ :=
begin
  simp, intros typeq streq,
  have fn := FN, 
  unfold F at fn,
  have fz : ∃ (o : ℤ), ∀ (i : ℤ), has_le.le o i := heq.rec_on streq fn,
end

#check heq
