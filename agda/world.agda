module world where

{--open import Level--}
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≤?_ ; suc ; s≤s)


{-- useful --}
data Unit : Set where
  Ax : Unit

True : Set
True = Unit

postulate
  {--  Worlds --}
  world : Set
  {-- w2 extends w1 --}
  _⪰_ : (w2 : world) → (w1 : world) → Set
  {-- extension is transitive --}
  extTrans : ∀ {w3 w2 w1} (e2 : w3 ⪰ w2) (e1 : w2 ⪰ w1) → w3 ⪰ w1

allW : ∀ (w : world) (f : ∀ (w' : world) (e : w' ⪰ w) → Set) → Set
allW w f = ∀ (w' : world) (e : w' ⪰ w) → f w' e

exW : ∀ (w : world) (f : ∀ (w' : world) (e : w' ⪰ w) → Set) → Set
exW w f = Σ world (λ w' → Σ (w' ⪰ w) (λ e → f w' e))

inOpenBar : ∀ (w : world) (f : ∀ (w' : world) (e : w' ⪰ w) → Set) → Set
inOpenBar w f = allW w (λ w1 e1 → exW w1 (λ w2 e2 → allW w2 (λ w3 e3 → f w3 (extTrans e3 (extTrans e2 e1)))))

{-- a dependent open bar --}
inOpenBar' : ∀ (w : world) {g} (h : inOpenBar w g) (f : ∀ (w' : world) (e : w' ⪰ w) (x : g w' e) → Set) → Set
inOpenBar' w h f =
  allW w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 →
             let e' = extTrans e3 e2 in
             f w3 (extTrans e' (extTrans e1 e0)) (q w3 e'))))


{--  Terms --}
postulate
  choice_sequence_name : Set

data Var : Set where
  var : ℕ → Var

data Term : Set where
  {-- Numbers --}
  NAT : Term
  QNAT : Term
  LT : Term → Term → Term
  QLT : Term → Term → Term
  NUM : ℕ → Term
  {-- PI Types --}
  PI :  Term → Var → Term → Term
  LAMBDA : Var → Term → Term
  APPLY : Term → Term → Term
  {-- SUM Types --}
  SUM : Term → Var → Term → Term
  PAIR : Term → Term → Term
  SPREAD : Term → Var → Var → Term
  {-- SET Types --- set types don't have constuctors/destructors --}
  SET : Term → Var → Term → Term
  {-- UNION Types --}
  UNION : Term → Term → Term
  INL : Term → Term
  INR : Term → Term
  DECIDE : Term → Var → Term → Var → Term
  {-- Equality Types --}
  EQ : Term → Term → Term → Term
  AX : Term
  {-- Choice sequences --}
  FREE : Term
  CS : choice_sequence_name → Term
  {-- Universes --}
  UNIV : ℕ → Term

postulate
  {-- standard subsitution function on terms --}
  subst : Var → Term → Term -> Term
  {-- operational semantics of the language --}
  _⇓_at_ : ∀ (T T' : Term) (w : world) → Set
infix 30 _⇓_at_

{-- T computes to T' in all extensions of w --}
_⇛_at_ : ∀ (T T' : Term) (w : world) → Set
T ⇛ T' at w = allW w (λ w' _ → T ⇓ T' at w')
infix 30 _⇛_at_

{-- t1 t2 have to compute to the same number and stay the same number in all extensions --}
strongMonEq : ∀ (w : world) (t1 t2 : Term) → Set
strongMonEq w t1 t2 = Σ ℕ (λ n → t1 ⇛ (NUM n) at w × t2 ⇛ (NUM n) at w)

{-- t1 t2 have to compute to the same number but that number can change over time --}
weakMonEq : ∀ (w : world) (t1 t2 : Term) → Set
weakMonEq w t1 t2 = allW w (λ w' _ → Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w'))

{-- Semantics --}
per : Set₁
per = Term → Term → Set

{-- the PER of all universes n less than m --}
univs : Set₁
univs = Σ ℕ (λ m → (n : ℕ) → (n < m) → per)

{--data lib_extends (u : univs) : world → world → Set--}
data eqTypes (u : univs) (w : world) (T1 T2 : Term) : Set
eqInType : (u : univs) (w : world) {T1 T2 : Term} → (eqTypes u w T1 T2) → per

data eqTypes u w T1 T2 where
  EQTNAT : T1 ⇛ NAT at w → T2 ⇛ NAT at w → eqTypes u w T1 T2
  EQTQNAT : T1 ⇛ QNAT at w → T2 ⇛ QNAT at w → eqTypes u w T1 T2
  EQTLT : (a1 a2 b1 b2 : Term)
    → T1 ⇛ (LT a1 b1) at w
    → T2 ⇛ (LT a2 b2) at w
    → strongMonEq w a1 a2
    → strongMonEq w b1 b2
    → eqTypes u w T1 T2
  EQTQLT : (a1 a2 b1 b2 : Term)
    → T1 ⇛ (QLT a1 b1) at w
    → T2 ⇛ (QLT a2 b2) at w
    → weakMonEq w a1 a2
    → weakMonEq w b1 b2
    → eqTypes u w T1 T2
  EQTFREE : T1 ⇛ FREE at w → T2 ⇛ FREE at w → eqTypes u w T1 T2
  EQTPI : (A1 B1 A2 B2 : Term) (v1 v2 : Var)
    → T1 ⇛ (PI A1 v1 B1) at w
    → T2 ⇛ (PI A2 v2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2 → eqTypes u w' (subst v1 a1 B1) (subst v2 a2 B2)))
    → eqTypes u w T1 T2
  EQTSUM : (A1 B1 A2 B2 : Term) (v1 v2 : Var)
    → T1 ⇛ (SUM A1 v1 B1) at w
    → T2 ⇛ (SUM A2 v2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2 → eqTypes u w' (subst v1 a1 B1) (subst v2 a2 B2)))
    → eqTypes u w T1 T2
  EQTSET : (A1 B1 A2 B2 : Term) (v1 v2 : Var)
    → T1 ⇛ (SET A1 v1 B1) at w
    → T2 ⇛ (SET A2 v2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2 → eqTypes u w' (subst v1 a1 B1) (subst v2 a2 B2)))
    → eqTypes u w T1 T2
  EQTEQ : (a1 b1 a2 b2 A B : Term)
    → T1 ⇛ (EQ a1 a2 A) at w
    → T2 ⇛ (EQ b1 b2 B) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A B))
    → (eqt1 : allW w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
    → (eqt2 : allW w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
    → eqTypes u w T1 T2
  EQTUNION : (A1 B1 A2 B2 : Term)
    → T1 ⇛ (UNION A1 B1) at w
    → T2 ⇛ (UNION A2 B2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtB : allW w (λ w' _ → eqTypes u w' B1 B2))
    → eqTypes u w T1 T2
  EQTUNIV : (n :  ℕ) (p : n <  proj₁ u) (c1 : T1 ⇛ (UNIV n) at w) (c2 : T2 ⇛ (UNIV n) at w)
          → eqTypes u w T1 T2
  EQTBAR : inOpenBar w (λ w' _ → eqTypes u w' T1 T2)
         → eqTypes u w T1 T2

eqInType _ w (EQTNAT _ _) t1 t2 =
  inOpenBar w (λ w' _ → strongMonEq w' t1 t2)
eqInType _ w (EQTQNAT _ _) t1 t2 =
  inOpenBar w (λ w' _ → weakMonEq w' t1 t2)
eqInType _ w (EQTLT a1 _ b1 _ _ _ _ _) t1 t2 =
  inOpenBar w (λ w' _ → Σ ℕ (λ n → Σ ℕ (λ m → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM m) at w' × n < m)))
eqInType _ w (EQTQLT a1 _ b1 _ _ _ _ _) t1 t2 =
  inOpenBar w (λ w' _ → Σ ℕ (λ n → Σ ℕ (λ m → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM m) at w' × n < m)))
eqInType _ w (EQTFREE _ _) t1 t2 =
  inOpenBar w (λ w' _ → Σ choice_sequence_name (λ n → t1 ⇛ (CS n) at w' × t2 ⇛ (CS n) at w'))
eqInType u w (EQTPI _ _ _ _ _ _ _ _ eqta eqtb) f1 f2 =
  inOpenBar w (λ w' e → ∀ (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2)
                      → eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY f1 a1) (APPLY f2 a2))
eqInType u w (EQTSUM _ _ _ _ _ _ _ _ eqta eqtb) t1 t2 =
  inOpenBar w (λ w' e → Σ Term (λ a1 → Σ Term (λ a2 → Σ Term (λ b1 → Σ Term (λ b2 → Σ (eqInType u w' (eqta w' e) a1 a2) (λ ea →
                         t1 ⇛ (PAIR a1 b1) at w'
                         × t2 ⇛ (PAIR a2 b2) at w'
                         × eqInType u w' (eqtb w' e a1 a2 ea) b1 b2))))))
eqInType u w (EQTSET _ _ _ _ _ _ _ _ eqta eqtb) t1 t2 =
  inOpenBar w (λ w' e → Σ Term (λ b → Σ (eqInType u w' (eqta w' e) t1 t2) (λ ea →
                         eqInType u w' (eqtb w' e t1 t2 ea) b b)))
eqInType u w (EQTEQ a1 b1 _ _ _ _ _ _ eqtA eqt1 eqt2) t1 t2 =
  inOpenBar w (λ w' e → t1 ⇛ AX at w' × t2 ⇛ AX at w' × eqInType u w' (eqtA w' e) a1 b1)
eqInType u w (EQTUNION _ _ _ _ _ _ eqtA eqtB) t1 t2 =
  inOpenBar w (λ w' e → (Σ Term (λ a → Σ Term (λ b →
                 (t1 ⇛ (INL a) at w' × t2 ⇛ (INR b) at w' × eqInType u w' (eqtA w' e) a b)
                 ⊎
                 (t1 ⇛ (INR a) at w' × t2 ⇛ (INR b) at w' × eqInType u w' (eqtB w' e) a b)))))
eqInType u w (EQTUNIV n p _ _) T1 T2 = proj₂ u n p T1 T2
eqInType u w (EQTBAR f) t1 t2 =
  {-- inOpenBar' w f (λ w' _ (x : eqTypes u w' _ _) → eqInType u w' x t1 t2)--}
  {-- The is an unfolding of the above, as the termination checker fails on the above --}
  allW w (λ w0 e0 →
           let p  = f w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 → eqInType u w3 (q w3 (extTrans e3 e2)) t1 t2)))


eqtypes : (m : ℕ) (w : world) → per
eqtypes 0 w t1 t2 = eqTypes (0 , λ _ _ _ _ → ⊥) w t1 t2
eqtypes (suc m) w t1 t2 = eqTypes (suc m , λ n p → eqtypes m w) w t1 t2

{--eqintype : (m : ℕ) (w : world) (T : Term) → per
eqintype m w T t1 t2 = Σ (eqtypes m w T T) (λ p → eqInType (m , λ n _ ) w T T p)--}

