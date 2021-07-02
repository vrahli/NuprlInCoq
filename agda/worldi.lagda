\documentclass{article}

\usepackage{agda}

\usepackage{amssymb}
\usepackage{fdsymbol}
\usepackage[utf8]{inputenc}
\usepackage{newunicodechar}

\newcommand{\nat}{\mathbb{N}}

\newunicodechar{ℕ}{\ensuremath{\mathnormal\nat}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{⪰}{\ensuremath{\mathnormal\succeq}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{←}{\ensuremath{\mathnormal\from}}
\newunicodechar{→}{\ensuremath{\mathnormal\to}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{Σ}{\ensuremath{\mathnormal\exists}}
\newunicodechar{₁}{\ensuremath{\mathnormal{}_{1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{}_{2}}}
\newunicodechar{⇓}{\ensuremath{\mathnormal\Downarrow}}
\newunicodechar{⇛}{\ensuremath{\mathnormal\Ddownarrow}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\cupplus}}
\newunicodechar{⊥}{\ensuremath{\mathnormal\bot}}
%$\newunicodechar{<}{\ensuremath{\mathnormal<}}
\newunicodechar{∼}{\ensuremath{\mathnormal\sim}}
\newunicodechar{≈}{\ensuremath{\mathnormal\approx}}

\begin{document}
\begin{footnotesize}

\begin{AgdaAlign}
\begin{code}[hide]
module worldi where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≤?_ ; suc)
\end{code}


We first postulate and define enough about worlds to interpret OpenTT
w.r.t. open bars.


\begin{code}
postulate
  --  Worlds
  world : Set
  -- w2 extends w1
  _⪰_ : (w2 : world) → (w1 : world) → Set
  -- extension is reflexive
  extRefl : ∀ w → w ⪰ w
  -- extension is transitive
  extTrans : ∀ {w3 w2 w1} (e2 : w3 ⪰ w2) (e1 : w2 ⪰ w1) → w3 ⪰ w1

wPred : (w : world) → Set₁
wPred w = ∀ (w' : world) (e : w' ⪰ w) → Set

wPredExtIrr : {w : world} (f : wPred w) → Set
wPredExtIrr {w} f = (w' : world) (e1 e2 : w' ⪰ w) → f w' e1 → f w' e2

record wPredEI (w : world) : Set₁ where
  field
    p : wPred w
    c : wPredExtIrr p

-- f holds in all extensions
allW : ∀ (w : world) (f : wPred w) → Set
allW w f = ∀ (w' : world) (e : w' ⪰ w) → f w' e

-- f holds in one extensions
exW : ∀ (w : world) (f : wPred w) → Set
exW w f = Σ world (λ w' → Σ (w' ⪰ w) (λ e → f w' e))

-- f holds in an open bar
inOpenBar : ∀ (w : world) (f : wPred w) → Set
inOpenBar w f =
  allW w (λ w1 e1 → exW w1 (λ w2 e2 → allW w2 (λ w3 e3 →
     f w3 (extTrans e3 (extTrans e2 e1)))))

-- f holds in an open bar that depends on another open bar h
inOpenBar' : ∀ w {g} (h : inOpenBar w g) (f : ∀ w' (e : w' ⪰ w) (x : g w' e) → Set) → Set
inOpenBar' w h f =
  allW w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 →
             let e' = extTrans e3 e2 in
             f w3 (extTrans e' (extTrans e1 e0)) (q w3 e'))))
\end{code}


We now define part of OpenTT's syntax and postulate its operational semantics.


\begin{code}
postulate
  choice_sequence_name : Set

data Var : Set where
  var : ℕ → Var -- variable are simply numbers

data Term : Set where
  -- Numbers
  NAT : Term
  QNAT : Term
  LT : Term → Term → Term
  QLT : Term → Term → Term
  NUM : ℕ → Term
  -- Products
  PI :  Term → Var → Term → Term
  LAMBDA : Var → Term → Term
  APPLY : Term → Term → Term
  -- Sums
  SUM : Term → Var → Term → Term
  PAIR : Term → Term → Term
  SPREAD : Term → Var → Var → Term
  -- Sets --- they don't have constructors/destructors
  SET : Term → Var → Term → Term
  -- Disjoint unions
  UNION : Term → Term → Term
  INL : Term → Term
  INR : Term → Term
  DECIDE : Term → Var → Term → Var → Term
  -- Equality
  EQ : Term → Term → Term → Term
  AX : Term
  -- Choice sequences
  FREE : Term
  CS : choice_sequence_name → Term
  -- Time squashing
  TSQUASH : Term → Term
  -- Free from definitions
  FFDEFS : Term → Term → Term
  -- Universes
  UNIV : ℕ → Term

isValue : Term → Set
isValue NAT = ⊤
isValue QNAT = ⊤
isValue (LT _ _) = ⊥
isValue (QLT _ _) = ⊥
isValue (NUM _) = ⊤
isValue (PI _ _ _) = ⊤
isValue (LAMBDA _ _) = ⊤
isValue (APPLY _ _) = ⊥
isValue (SUM _ _ _) = ⊤
isValue (PAIR _ _) = ⊤
isValue (SPREAD _ _ _) = ⊥
isValue (SET _ _ _) = ⊤
isValue (UNION _ _) = ⊤
isValue (INL _) = ⊤
isValue (INR _) = ⊤
isValue (DECIDE _ _ _ _) = ⊥
isValue (EQ _ _ _) = ⊤
isValue AX = ⊤
isValue FREE = ⊤
isValue (CS _) = ⊤
isValue (TSQUASH _) = ⊤
isValue (FFDEFS _ _) = ⊤
isValue (UNIV _) = ⊤

postulate
  -- standard substitution function on terms
  sub : Var → Term → Term → Term
  -- operational semantics of the language
  _⇓_at_ : ∀ (T T' : Term) (w : world) → Set
  -- 'computes to' is reflexive
  compRefl : ∀ (T : Term) (w : world) → T ⇓ T at w
  -- values compute to themselves
  compVal : ∀ (a b : Term) (w : world) → a ⇓ b at w → isValue a → a ≡ b
  -- Howe's computational equivalence relation
  _∼_at_ : ∀ (T T' : Term) (w : world) → Set
  -- states that the argument does not contain any definition or choice sequence
  nodefs : Term → Set
infix 30 _⇓_at_
infix 30 _∼_at_

-- T computes to T' in all extensions of w
_⇛_at_ : ∀ (T T' : Term) (w : world) → Set
T ⇛ T' at w = allW w (λ w' _ → T ⇓ T' at w')
infix 30 _⇛_at_

-- T computationally equivalent to T' in all extensions of w
_≈_at_ : ∀ (T T' : Term) (w : world) → Set
T ≈ T' at w = allW w (λ w' _ → T ∼ T' at w')
infix 30 _≈_at_

compAllRefl : ∀ (T : Term) (w : world) → T ⇛ T at w
compAllRefl T w =  λ w' e → compRefl T w'

-- t1 and t2 compute to the same number and stay the same number in all extensions
strongMonEq : ∀ (w : world) (t1 t2 : Term) → Set
strongMonEq w t1 t2 = Σ ℕ (λ n → t1 ⇛ (NUM n) at w × t2 ⇛ (NUM n) at w)

-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : ∀ (w : world) (t1 t2 : Term) → Set
weakMonEq w t1 t2 = allW w (λ w' _ → Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w'))
\end{code}


We now provide an inductive-recursive realizability semantics of
OpenTT.


\begin{code}
-- PERs and world dependent PERs
per : Set₁
per = Term → Term → Set

wper : Set₁
wper = world → per

-- eqTypes and eqInType provide meaning to types w.r.t. already interpreted universes,
-- given by univs (1st conjunct defines the equality between such universes, while the
-- second conjunct defines the equality in such universes)
univs : Set₁
univs = Σ ℕ (λ n → wper × wper)

-- equality between types (an inductive definition)
-- and equality in types (a recursive function)
data eqTypes (u : univs) (w : world) (T1 T2 : Term) : Set
eqInType : (u : univs) (w : world) {T1 T2 : Term} → (eqTypes u w T1 T2) → per
\end{code}


Equality between type is defined as the following inductive definition


\begin{code}
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
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub v1 a1 B1) (sub v2 a2 B2)))
    → eqTypes u w T1 T2
  EQTSUM : (A1 B1 A2 B2 : Term) (v1 v2 : Var)
    → T1 ⇛ (SUM A1 v1 B1) at w
    → T2 ⇛ (SUM A2 v2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub v1 a1 B1) (sub v2 a2 B2)))
    → eqTypes u w T1 T2
  EQTSET : (A1 B1 A2 B2 : Term) (v1 v2 : Var)
    → T1 ⇛ (SET A1 v1 B1) at w
    → T2 ⇛ (SET A2 v2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub v1 a1 B1) (sub v2 a2 B2)))
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
  EQTSQUASH : (A1 A2 : Term)
    → T1 ⇛ (TSQUASH A1) at w
    → T2 ⇛ (TSQUASH A2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → eqTypes u w T1 T2
  EQFFDEFS : (A1 A2 x1 x2 : Term)
    → T1 ⇛ (FFDEFS A1 x1) at w
    → T2 ⇛ (FFDEFS A2 x2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqx : allW w (λ w' e → eqInType u w' (eqtA w' e) x1 x1))
    → eqTypes u w T1 T2
  EQTUNIV : proj₁ (proj₂ u) w T1 T2 → eqTypes u w T1 T2
  EQTBAR : inOpenBar w (λ w' _ → eqTypes u w' T1 T2) → eqTypes u w T1 T2
\end{code}


Equality in types is defined as the following recursive function.


\begin{code}
eqInType _ w (EQTNAT _ _) t1 t2 = inOpenBar w (λ w' _ → strongMonEq w' t1 t2)
eqInType _ w (EQTQNAT _ _) t1 t2 = inOpenBar w (λ w' _ → weakMonEq w' t1 t2)
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
  inOpenBar w (λ w' e → Σ Term (λ a1 → Σ Term (λ a2 → Σ Term (λ b1 → Σ Term (λ b2 →
                         Σ (eqInType u w' (eqta w' e) a1 a2) (λ ea →
                         t1 ⇛ (PAIR a1 b1) at w'
                         × t2 ⇛ (PAIR a2 b2) at w'
                         × eqInType u w' (eqtb w' e a1 a2 ea) b1 b2))))))
eqInType u w (EQTSET _ _ _ _ _ _ _ _ eqta eqtb) t1 t2 =
  inOpenBar w (λ w' e → Σ Term (λ b → Σ (eqInType u w' (eqta w' e) t1 t2) (λ ea →
                         eqInType u w' (eqtb w' e t1 t2 ea) b b)))
eqInType u w (EQTEQ a1 b1 _ _ _ _ _ _ eqtA eqt1 eqt2) t1 t2 =
  inOpenBar w (λ w' e → t1 ⇛ AX at w' × t2 ⇛ AX at w' × eqInType u w' (eqtA w' e) a1 b1)
eqInType u w (EQTUNION _ _ _ _ _ _ eqtA eqtB) t1 t2 =
  inOpenBar w (λ w' e → Σ Term (λ a → Σ Term (λ b →
                 (t1 ⇛ (INL a) at w' × t2 ⇛ (INR b) at w' × eqInType u w' (eqtA w' e) a b)
                 ⊎
                 (t1 ⇛ (INR a) at w' × t2 ⇛ (INR b) at w' × eqInType u w' (eqtB w' e) a b))))
eqInType u w (EQTSQUASH _ _ _ _ eqtA) t1 t2 =
  inOpenBar w (λ w' e → Σ Term (λ a1 → Σ Term (λ a2 →
                 (t1 ∼ a1 at w') × (t2 ∼ a2 at w') × (t1 ≈ t2 at w')
                 × eqInType u w' (eqtA w' e) a1 a2)))
eqInType u w (EQFFDEFS _ _ x1 _ _ _ eqtA _) t1 t2 =
  inOpenBar w (λ w' e → Σ Term (λ x →
                (t1 ⇛ AX at w') × (t2 ⇛ AX at w')
                × eqInType u w' (eqtA w' e) x1 x × nodefs x))
eqInType u w (EQTUNIV _) T1 T2 = proj₂ (proj₂ u) w T1 T2
eqInType u w (EQTBAR f) t1 t2 =
  {-- inOpenBar' w f (λ w' _ (x : eqTypes u w' _ _) → eqInType u w' x t1 t2)--}
  {-- This is an unfolding of the above, as agda doesn't like the above --}
  allW w (λ w0 e0 →
           let p  = f w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 → eqInType u w3 (q w3 (extTrans e3 e2)) t1 t2)))
\end{code}


We finally close the construction as follows:


\begin{code}
-- Two level-m universes are equal if they compute to (UNIV m)
eqUnivi : (m : ℕ) → wper
eqUnivi m w T1 T2 = inOpenBar w (λ w' _ → T1 ⇛ (UNIV m) at w' × T2 ⇛ (UNIV m) at w')

-- Two terms are equal in universe m if they are equal according to eqTypes
eqInUnivi : (m : ℕ) → wper
eqInUnivi 0 = λ _ _ _ → ⊥
eqInUnivi (suc m) w T1 T2 = eqTypes (m , (eqUnivi m , eqInUnivi m)) w T1 T2 ⊎ eqInUnivi m w T1 T2

uni : ℕ → univs
uni n = (n , (eqUnivi n , eqInUnivi n))

-- Finally, the 'equal types' and 'equal in types' relations
eqtypes : (w : world) (T1 T2 : Term) → Set
eqtypes w T1 T2 = Σ ℕ (λ n → eqTypes (uni n) w T1 T2)

eqintype : (w : world) (T a b : Term) → Set
eqintype w T a b = Σ ℕ (λ n → Σ (eqTypes (uni n) w T T) (λ p → eqInType (uni n) w p a b))
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]
univInBar : (n : ℕ) (w : world) → eqUnivi n w (UNIV n) (UNIV n)
univInBar n w =  λ w0 e0 →  ( w0 ,  (  extRefl w0 ,  λ w1 e1 →  ( compAllRefl (UNIV n) w1 , compAllRefl (UNIV n) w1 ) ) )

lemma1 : (w : world) → eqtypes w (UNIV 0) (UNIV 0)
lemma1 w = (0 , EQTUNIV ( univInBar 0 w))

lemma2 : (w : world) → eqtypes w (UNIV 1) (UNIV 1)
lemma2 w = (1 , EQTUNIV ( univInBar 1 w))

lemma3 : (w : world) → eqintype w (UNIV 1) (UNIV 0) (UNIV 0)
lemma3 w = (1 , snd (lemma2 w) ,  inj₁ (EQTUNIV (univInBar 0 w)) )

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

UNIVinj : {n m : ℕ} → UNIV n ≡ UNIV m → n ≡ m
UNIVinj refl =  refl

UNIVn1 : {n : ℕ} → ¬ UNIV n ≡ NAT
UNIVn1 {n} ()

UNIVn2 : {n : ℕ} → ¬ UNIV n ≡ QNAT
UNIVn2 {n} ()

UNIVn3 : {n : ℕ} {a b : Term} → ¬ UNIV n ≡ LT a b
UNIVn3 {n} ()

UNIVn4 : {n : ℕ} {a b : Term} → ¬ UNIV n ≡ QLT a b
UNIVn4 {n} ()

UNIVn5 : {n : ℕ} → ¬ UNIV n ≡ FREE
UNIVn5 {n} ()

UNIVn6 : {n : ℕ} {a : Term} {v : Var} {b : Term} → ¬ UNIV n ≡ PI a v b
UNIVn6 {n} ()

UNIVn7 : {n : ℕ} {a : Term} {v : Var} {b : Term} → ¬ UNIV n ≡ SUM a v b
UNIVn7 {n} ()

UNIVn8 : {n : ℕ} {a : Term} {v : Var} {b : Term} → ¬ UNIV n ≡ SET a v b
UNIVn8 {n} ()

UNIVn9 : {n : ℕ} {a b c : Term} → ¬ UNIV n ≡ EQ a b c
UNIVn9 {n} ()

UNIVn10 : {n : ℕ} {a b : Term} → ¬ UNIV n ≡ UNION a b
UNIVn10 {n} ()

UNIVn11 : {n : ℕ} {a : Term} → ¬ UNIV n ≡ TSQUASH a
UNIVn11 {n} ()

UNIVn12 : {n : ℕ} {a b : Term} → ¬ UNIV n ≡ FFDEFS a b
UNIVn12 {n} ()

compUNIV : (w : world) {n : ℕ} {a : Term} → UNIV n ⇛ a at w → a ≡ UNIV n
compUNIV w c = sym ((compVal _ _ _ (c w (extRefl w))) tt)

eqU : (n m : ℕ) (w : world) → eqUnivi n w (UNIV m) (UNIV m) → n ≡ m
eqU n m w =  λ p → let (a , (b , c)) = p w (extRefl w) in
                    let (c1 , c2) = c (proj₁ (p w (extRefl w))) (extRefl (proj₁ (p w (extRefl w)))) in
                    sym (UNIVinj (compVal _ _ _ (c2 (proj₁ (p w (extRefl w))) (extRefl (proj₁ (p w (extRefl w))))) tt))

neq01 : ¬ 0 ≡ 1
neq01 ()

allWMP : (w : world) (f g : wPred w)
         → (h : (w' : world) (e : w' ⪰ w) → f w' e → g w' e)
         → allW w f → allW w g
allWMP w f g h a w' e =  h _ e (a _ e)

inOpenBarMP : (w : world) (f g : wPred w)
              → (h : (w' : world) (e : w' ⪰ w) → f w' e → g w' e)
              → inOpenBar w f → inOpenBar w g
inOpenBarMP w f g h i w' e =
  let (w1 , (e1 , z)) = i _ e in
  (w1 , (e1 , allWMP _ _ _ (λ w'' e'' hf → h _ (extTrans e'' (extTrans e1 e)) hf) z))

inOpenBarIdem : (w : world) (f : wPred w) (c : wPredExtIrr f)
                → inOpenBar w (λ w1 e1 → inOpenBar w1 (λ w2 e2 → f w2 (extTrans e2 e1))) → inOpenBar w f
inOpenBarIdem w f c i w1 e1 =
  let (w2 , (e2 , z)) = i _ e1 in
  let (w3 , (e3 , x)) = z _ (extRefl _) _ (extRefl _) in
   (_ , (extTrans e3 e2 , λ w4 e4 → let h = x _ e4 in c _ _ _ h))

mon : (p : wper) → Set
mon p = (a b : Term) (w : world) → p w a b → (w' : world) (e : w' ⪰ w) → p w' a b

inOpenBarIfMon : (p : wper) (w : world) (a b : Term) → mon p → p w a b → inOpenBar w (λ w' e → p w' a b)
inOpenBarIfMon p w a b m h w1 e1 = (w1 , (extRefl _ , λ w2 e2 → m _ _ _ h w2 (extTrans e2 e1)))

monUnivs : (u : univs) → Set
monUnivs u = mon (proj₁ (snd u))

wPredExtIrrUnivs : (u : univs) → Set
wPredExtIrrUnivs u = (w : world) (a b : Term) → wPredExtIrr (λ (w' : world) (e : w' ⪰ w) → proj₁ (snd u) w' a b)

eqTypesU : (u : univs) (m : monUnivs u) (w : world) (n : ℕ)
           → eqTypes u w (UNIV n) (UNIV n)
           → inOpenBar w (λ w' _ → proj₁ (proj₂ u) w' (UNIV n) (UNIV n))
eqTypesU u m w n (EQTNAT x x₁) =  ⊥-elim (UNIVn1 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTQNAT x x₁) = ⊥-elim (UNIVn2 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (UNIVn3 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (UNIVn4 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTFREE x x₁) = ⊥-elim (UNIVn5 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTPI A1 B1 A2 B2 v1 v2 x x₁ eqta eqtb) = ⊥-elim (UNIVn6 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTSUM A1 B1 A2 B2 v1 v2 x x₁ eqta eqtb) = ⊥-elim (UNIVn7 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTSET A1 B1 A2 B2 v1 v2 x x₁ eqta eqtb) = ⊥-elim (UNIVn8 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) = ⊥-elim (UNIVn9 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (UNIVn10 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTSQUASH A1 A2 x x₁ eqtA) = ⊥-elim (UNIVn11 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = ⊥-elim (UNIVn12 (sym (compUNIV _ x₁)))
eqTypesU u m w n (EQTUNIV x) = inOpenBarIfMon _ _ _ _ m x
eqTypesU u m w n (EQTBAR x) = λ w1 e1 →
  let (w2 , (e2 , z)) = x _ e1 in
  let ih = eqTypesU u m _ _ (z _ (extRefl _)) in
  let (w3 , (e3 , z1)) = ih _ (extRefl _) in
  (w3 , (extTrans e3 e2 , λ w4 e4 → z1 _ e4))

monEqUnivi : (n : ℕ) → mon (eqUnivi n)
monEqUnivi n a b w h w' e' w1 e1 = h _ (extTrans e1 e')

monUni : (n : ℕ) → monUnivs (uni n)
monUni n a b w h w' e' = monEqUnivi n _ _ _ h _ e'

neqiU1 : (w : world) → ¬ eqInUnivi 1 w (UNIV 1) (UNIV 1)
neqiU1 w (inj₁ x) =
  let (w1 , (e1 , z1)) = eqTypesU _ (monUni 0) _ _ x _ (extRefl _) in
  let (w2 , (e2 , z2)) = z1 _ (extRefl _) _ (extRefl _) in
  let (c1 , c2) = z2 _ (extRefl _) in
  neq01 (UNIVinj (compUNIV _ c1))

lemma4 : (w : world) → ¬ (eqintype w (UNIV 1) (UNIV 1) (UNIV 1))
lemma4 w =  λ p →  case p of λ {
  (n , EQTUNIV x , b) → neqiU1 _ (subst (λ n₁ → snd (snd (uni n₁)) w (UNIV 1) (UNIV 1)) (eqU _ _ _ x) b) ;
  (n , EQTNAT x x₁ , b) → ⊥-elim (UNIVn1 (sym (compUNIV _ x₁))) ;
  (n , EQTQNAT x x₁ , b) → ⊥-elim (UNIVn2 (sym (compUNIV _ x₁))) ;
  (n , EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , b) → ⊥-elim (UNIVn3 (sym (compUNIV _ x₁))) ;
  (n , EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , b) → ⊥-elim (UNIVn4 (sym (compUNIV _ x₁))) ;
  (n , EQTFREE x x₁ , b) → ⊥-elim (UNIVn5 (sym (compUNIV _ x₁))) ;
  (n , EQTPI A1 B1 A2 B2 v1 v2 x x₁ eqta eqtb , b) → ⊥-elim (UNIVn6 (sym (compUNIV _ x₁))) ;
  (n , EQTSUM A1 B1 A2 B2 v1 v2 x x₁ eqta eqtb , b) → ⊥-elim (UNIVn7 (sym (compUNIV _ x₁))) ;
  (n , EQTSET A1 B1 A2 B2 v1 v2 x x₁ eqta eqtb , b) → ⊥-elim (UNIVn8 (sym (compUNIV _ x₁))) ;
  (n , EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , b) → ⊥-elim (UNIVn9 (sym (compUNIV _ x₁))) ;
  (n , EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , b) → ⊥-elim (UNIVn10 (sym (compUNIV _ x₁))) ;
  (n , EQTSQUASH A1 A2 x x₁ eqtA , b) → ⊥-elim (UNIVn11 (sym (compUNIV _ x₁))) ;
  (n , EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , b) → ⊥-elim (UNIVn12 (sym (compUNIV _ x₁))) ;
  (n , EQTBAR x , b) →
    let (w1 , (e1 , z)) = b _ (extRefl _) in
    let z' = z _ (extRefl _) in
    lemma4 _ (n , ((snd (snd (x w (extRefl w))) (proj₁ (b w (extRefl w)))
      (extTrans (extRefl (proj₁ (b w (extRefl w))))
       (proj₁ (snd (b w (extRefl w)))))) , z'))
  }

\end{code}
\end{AgdaAlign}
\end{footnotesize}
\end{document}
