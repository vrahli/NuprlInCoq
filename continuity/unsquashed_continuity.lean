open quot
open nat

inductive Unit : Prop :=
| it : Unit

definition eqTrue {T : Type} (a b : T) : Prop := Unit

theorem eqTrue_equiv : forall {T : Type}, equivalence (@eqTrue T) :=
begin
intro T,
split,

rewrite ↑[reflexive, eqTrue], intro x, apply Unit.it,

split,

rewrite ↑[symmetric, eqTrue], intros x y z, apply Unit.it,

rewrite ↑[transitive, eqTrue], intros x y z v w, apply Unit.it
end

definition setoidTrue {T : Type} : setoid T := setoid.mk eqTrue eqTrue_equiv

definition qsquash (T : Type) := @quot T setoidTrue

definition qnat := qsquash ℕ

definition qsig (A : Type) (B : A → Type) : Type :=
  qsquash (sigma B)

theorem has_lt_nat : has_lt ℕ := nat.nat_has_lt

definition baire := ℕ → ℕ

definition eq_upto (f g : baire) (n : ℕ) :=
  forall x : nat, x < n → f x = g x

definition continuity :=
  forall F : baire → ℕ,
  forall f : baire,
   Σ n : nat,
     forall g : baire,
     eq_upto f g n
     → F f = F g
