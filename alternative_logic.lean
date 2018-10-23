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
| amp (p q) : prf (p →' (p →' q) →' q) -- internal modus ponnens, i couldn't prove it, can you?
| cn (p q r) : prf (q →' r) → prf (p →' q) → prf (p →' r)
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

lemma deduct (P Q : fml) : prf ((P →' Q) →' P →' Q) :=
    begin
        apply reflex,
    end

lemma deduction (P Q : fml) : prf ((P →' (P →' Q)) →' (P →' Q)) :=
    begin
        apply prf.mp (P →' ((P →' Q) →' Q)),
        apply prf.amp,
        apply prf.axs,
    end

lemma yesyes (Q : fml) : prf (¬'(¬'Q) →' Q) :=
    begin
        have H4213 : prf ((¬'(¬'(¬'(¬'Q))) →' ¬'(¬'Q)) →' (¬'Q →' ¬'(¬'(¬'Q)))),
            apply prf.axn,
        have H1320 : prf ((¬'Q →' ¬'(¬'(¬'Q))) →' (¬'(¬'Q) →' Q)),
            apply prf.axn,
        have H4220 : prf ((¬'(¬'(¬'(¬'Q))) →' ¬'(¬'Q)) →' (¬'(¬'Q) →' Q)),
            apply prf.cn (¬'(¬'(¬'(¬'Q))) →' ¬'(¬'Q)) ((¬'Q →' ¬'(¬'(¬'Q)))) (¬'(¬'Q) →' Q),
            exact H1320, exact H4213,
        have H242 : prf (¬'(¬'Q) →' ((¬'(¬'(¬'(¬'Q)))) →'(¬'(¬'Q)))),
            apply prf.axk,
        have H2020 : prf ((¬' (¬' Q) →' Q) →' (¬' (¬' Q) →' Q)),
            apply reflex,
        have H220 : prf (¬' (¬' Q) →' (¬' (¬' Q) →' Q)),
            apply prf.cn _ ((¬'(¬'(¬'(¬'Q)))) →'(¬'(¬'Q))),
            exact H4220,
            exact H242,
        apply prf.mp (¬' (¬' Q) →' ¬' (¬' Q) →' Q),
        exact H220,
        apply deduction,
    end

theorem notnot (P : fml) : prf (P →' ¬'(¬'P)) :=
    begin
        have H31 : prf (¬'(¬'(¬'P)) →' ¬' P),
            apply yesyes,
        apply prf.mp (¬' (¬' (¬' P)) →' ¬' P),
        exact H31,
        apply prf.axn,
    end