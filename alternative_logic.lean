inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)
open fml

infixr ` →' `:50 := imp
local notation ` ¬' ` := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : prf $ (¬'q →' ¬'p) →' p →' q
| mp (p q) : prf p → prf (p →' q) → prf q

theorem reflex (P : fml) : prf (P →' P) :=
    begin
        have R : fml, exact P,
        let Q : fml := R →' P,
        have HPQ : prf (P →' Q),
            change prf (P →' (R →' P)),
            apply prf.axk,
        have HPQP : prf (P →' (Q →' P)),
            apply prf.axk,
        have HPQPP : prf ((P →' Q) →' (P →' P)),
            apply prf.mp (P →' Q →' P),
            exact HPQP,
            apply prf.axs,
        apply prf.mp (P →' Q),
        exact HPQ,
        exact HPQPP,
    end

lemma deduce (P Q : fml) : prf (P →' (P →' Q) →' Q) :=
    begin
        sorry,
    end

lemma deduction (P Q : fml) : prf ((P →' (P →' Q)) →' (P →' Q)) :=
    begin
        apply prf.mp (P →' ((P →' Q) →' Q)),
        apply deduce,
        apply prf.axs,
    end

lemma yesyes (P : fml) : prf (¬'(¬'P) →' P) :=
    begin

    end

theorem notnot (P : fml) : prf (P →' ¬'(¬'P)) :=
    begin

    end