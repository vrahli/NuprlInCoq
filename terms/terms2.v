(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export Eqdep.
Require Export FunctionalExtensionality.
Require Export terms.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(* begin hide *)

Inductive obool : Type :=
| otrue  : obool
| ofalse : obool
| obseq  : (nat -> obool) -> obool.

Definition bool2obool (b : bool) : obool :=
  if b then otrue else ofalse.

Fixpoint oband (ob1 ob2 : obool) : obool :=
  match ob1 with
    | otrue => ob2
    | ofalse => ob1
    | obseq f =>
      match ob2 with
        | otrue => ob1
        | ofalse => ob2
        | obseq g => obseq (fun n => oband (f n) (g n))
      end
  end.

Fixpoint oball (l : list obool) : obool :=
  match l with
    | [] => otrue
    | o :: l => oband o (oball l)
  end.

Fixpoint term2otrue {o} (t : @NTerm o) : obool :=
  match t with
    | vterm _ => otrue
    | oterm op bts => oball (map bterm2otrue bts)
  end
with bterm2otrue {o} (bt : BTerm) : obool :=
       match bt with
         | bterm vars t => term2otrue t
       end.

Fixpoint no_const {o} (t : @NTerm o) : bool :=
  match t with
    | vterm _ => true
    | oterm o bs => no_const_o o && ball (map no_const_b bs)
  end
with no_const_b {o} (bt : @BTerm o) : bool :=
       match bt with
         | bterm _ t => no_const t
       end.

Fixpoint no_oconst {o} (t : @NTerm o) : obool :=
  match t with
    | vterm _ => otrue
    | oterm o bs => oband (bool2obool (no_const_o o)) (oball (map no_oconst_b bs))
  end
with no_oconst_b {o} (bt : @BTerm o) : obool :=
       match bt with
         | bterm _ t => no_oconst t
       end.

Lemma fold_nobnd {p} :
  forall t : @NTerm p, bterm [] t = nobnd t.
Proof.
  unfold nobnd; auto.
Qed.


Definition mk_integer {p} n : @NTerm p := oterm (Can (Nint n)) [].

Definition mk_nat {p} (n : nat) : @NTerm p := mk_integer (Z_of_nat n).

Definition mk_uni {p} n : @NTerm p := oterm (Can (NUni n)) [].

Definition mk_tuni {p} n : @NTerm p := oterm (NCan NTUni) [nobnd n].

Definition mk_minus {p} n : @NTerm p := oterm (NCan NMinus) [nobnd n].

Definition mk_base  {p} : @NTerm p := oterm (Can NBase)  [].
Definition mk_int   {p} : @NTerm p := oterm (Can NInt)   [].
Definition mk_atom  {p} : @NTerm p := oterm (Can NAtom)  [].
Definition mk_uatom {p} : @NTerm p := oterm (Can NUAtom) [].

Definition mk_pair {p} (a b : @NTerm p) := oterm (Can NPair) [nobnd a , nobnd b].

Definition mk_sup {p} (a b : @NTerm p) := oterm (Can NSup) [nobnd a , nobnd b].

Definition mk_refl {p} (a : @NTerm p) := oterm (Can NRefl) [nobnd a].

Definition mk_texc {p} (T1 T2 : @NTerm p) := oterm (Can NTExc) [nobnd T1, nobnd T2].

Definition mk_union {p} (T1 T2 : @NTerm p) := oterm (Can NUnion) [nobnd T1, nobnd T2].
Definition mk_eunion {p} (T1 T2 : @NTerm p) := oterm (Can NEUnion) [nobnd T1, nobnd T2].

Definition mk_union2 {p} (T1 T2 : @NTerm p) := oterm (Can NUnion2) [nobnd T1, nobnd T2].

Definition mk_approx {p} (a b : @NTerm p) := oterm (Can NApprox) [nobnd a , nobnd b].
Definition mk_cequiv {p} (a b : @NTerm p) := oterm (Can NCequiv) [nobnd a , nobnd b].

Definition mk_compute {p} (a b n : @NTerm p) := oterm (Can NCompute) [nobnd a , nobnd b , nobnd n].

Definition mk_free_from_atom {p} (a b c : @NTerm p) :=
  oterm (Can NFreeFromAtom) [nobnd a,nobnd b,nobnd c].

Definition mk_efree_from_atom {p} (a b c : @NTerm p) :=
  oterm (Can NEFreeFromAtom) [nobnd a,nobnd b,nobnd c].

Definition mk_free_from_atoms {p} (T t : @NTerm p) :=
  oterm (Can NFreeFromAtoms) [nobnd T, nobnd t].

Definition mk_free_from_defs {p} (T t : @NTerm p) :=
  oterm (Can NFreeFromDefs) [nobnd T, nobnd t].

Definition mk_requality {p} (t1 t2 T : @NTerm p) :=
  oterm (Can NREquality) [nobnd t1,nobnd t2,nobnd T].

Definition mk_tequality {p} (t1 t2 : @NTerm p) :=
  oterm (Can NTEquality) [nobnd t1,nobnd t2].

Definition mk_can_test {p} test (a b c : @NTerm p) :=
  oterm (NCan (NCanTest test)) [nobnd a,nobnd b,nobnd c].

Definition mk_ispair   {p} := @mk_can_test p CanIspair.
Definition mk_isint    {p} := @mk_can_test p CanIsint.
Definition mk_isinl    {p} := @mk_can_test p CanIsinl.
Definition mk_isinr    {p} := @mk_can_test p CanIsinr.
Definition mk_isaxiom  {p} := @mk_can_test p CanIsaxiom.
Definition mk_islambda {p} := @mk_can_test p CanIslambda.
Definition mk_isatom   {p} := @mk_can_test p CanIsatom.
Definition mk_isuatom  {p} := @mk_can_test p CanIsuatom.

Definition mk_rec {p} (v : NVar) (T : @NTerm p) :=
  oterm (Can NRec) [bterm [v] T].

Definition mk_image {p} (T f : @NTerm p) :=
  oterm (Can NImage) [nobnd T, nobnd f].

Definition mk_function {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NFunction) [nobnd T1, bterm [v] T2].

Definition mk_product {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NProduct) [nobnd T1, bterm [v] T2].

Definition mk_set {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NSet) [nobnd T1, bterm [v] T2].

Definition mk_tunion {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NTUnion) [nobnd T1, bterm [v] T2].

Definition mk_quotient {p} (T1 : @NTerm p) (v1 v2 : NVar) (T2 : NTerm) :=
  oterm (Can NQuotient) [nobnd T1, bterm [v1,v2] T2].

Definition mk_isect {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NIsect) [nobnd T1, bterm [v] T2].

Definition mk_disect {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NDIsect) [nobnd T1, bterm [v] T2].

Definition mk_eisect {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NEIsect) [nobnd T1, bterm [v] T2].

Definition mk_w {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NW) [nobnd T1, bterm [v] T2].

Definition mk_m {p} (T1 : @NTerm p) (v : NVar) (T2 : NTerm) :=
  oterm (Can NM) [nobnd T1, bterm [v] T2].

Definition mk_pw {p}
           (P : @NTerm p)
           (ap : NVar) (A : NTerm)
           (bp : NVar) (ba : NVar) (B : NTerm)
           (cp : NVar) (ca : NVar) (cb : NVar) (C : NTerm)
           (p : NTerm) :=
  oterm (Can NPW)
        [ nobnd P,
          bterm [ap] A,
          bterm [bp; ba] B,
          bterm [cp; ca; cb] C,
          nobnd p
        ].

Definition mk_pm {p}
           (P : @NTerm p)
           (ap : NVar) (A : NTerm)
           (bp : NVar) (ba : NVar) (B : NTerm)
           (cp : NVar) (ca : NVar) (cb : NVar) (C : NTerm)
           (p : NTerm) :=
  oterm (Can NPM)
        [ nobnd P,
          bterm [ap] A,
          bterm [bp; ba] B,
          bterm [cp; ca; cb] C,
          nobnd p
        ].

Definition mk_spread {p} (t1 : @NTerm p) (u v : NVar) (t2 : NTerm) :=
  oterm (NCan NSpread) [nobnd t1, bterm [u, v] t2].

Definition mk_dsup {p} (t1 : @NTerm p) (u v : NVar) (t2 : NTerm) :=
  oterm (NCan NDsup) [nobnd t1, bterm [u, v] t2].

Definition mk_decide {p} (t : @NTerm p) (u : NVar) (t1 : NTerm) (v : NVar) (t2 : NTerm) :=
  oterm (NCan NDecide) [nobnd t, bterm [u] t1, bterm [v] t2].

Definition mk_cbv {p} (t1 : @NTerm p) (v : NVar) (t2 : NTerm) :=
  oterm (NCan NCbv) [nobnd t1, bterm [v] t2].

Definition mk_try {p} (t1 : @NTerm p) (a : @NTerm p) (v : NVar) (t2 : NTerm) :=
  oterm (NCan NTryCatch) [nobnd t1, nobnd a, bterm [v] t2].

Definition mk_fresh {p} (v : NVar) (t : @NTerm p) :=
  oterm (NCan NFresh) [bterm [v] t].

Definition mk_sleep {p} (t : @NTerm p) := oterm (NCan NSleep) [nobnd t].

Definition mk_pertype {p} (R : @NTerm p) :=
  oterm (Can NEPertype) [nobnd R].

Definition mk_ipertype {p} (R : @NTerm p) :=
  oterm (Can NIPertype) [nobnd R].

Definition mk_spertype {p} (R : @NTerm p) :=
  oterm (Can NSPertype) [nobnd R].

Definition mk_partial {p} (T : @NTerm p) :=
  oterm (Can NPartial) [nobnd T].

Definition mk_admiss {p} (T : @NTerm p) :=
  oterm (Can NAdmiss) [nobnd T].

Definition mk_mono {p} (T : @NTerm p) :=
  oterm (Can NMono) [nobnd T].

Definition mk_less {p} (a b c d : @NTerm p) :=
  oterm (NCan (NCompOp CompOpLess)) [nobnd a, nobnd b, nobnd c, nobnd d].

Definition mk_int_eq {p} (a b c d : @NTerm p) :=
  oterm (NCan (NCompOp CompOpEq)) [nobnd a, nobnd b, nobnd c, nobnd d].

Definition mk_atom_eq {p} (a b c d : @NTerm p) :=
  oterm (NCan (NCompOp CompOpEq)) [nobnd a, nobnd b, nobnd c, nobnd d].

Definition mk_parallel {p} (a b : @NTerm p) := oterm (NCan NParallel) [nobnd a, nobnd b].

Definition mk_add {p} (a b : @NTerm p) := oterm (NCan (NArithOp ArithOpAdd)) [nobnd a, nobnd b].
Definition mk_mul {p} (a b : @NTerm p) := oterm (NCan (NArithOp ArithOpMul)) [nobnd a, nobnd b].
Definition mk_sub {p} (a b : @NTerm p) := oterm (NCan (NArithOp ArithOpSub)) [nobnd a, nobnd b].
Definition mk_div {p} (a b : @NTerm p) := oterm (NCan (NArithOp ArithOpDiv)) [nobnd a, nobnd b].
Definition mk_rem {p} (a b : @NTerm p) := oterm (NCan (NArithOp ArithOpRem)) [nobnd a, nobnd b].

Definition mk_omega {p} : @NTerm p := oterm (Can NOmega) [].
Definition mk_constant_p {p} (x : get_pconstP p) := oterm (Can (NConstP x)) [].
Definition mk_constant_t {p} (x : get_pconstT p) := oterm (Can (NConstT x)) [].

(*
Definition mk_esquash (R : NTerm) :=
  oterm (Can NEsquash) [nobnd R].
*)


(* Picks a variable that is not in the set of free variables of a given term *)
Definition newvar {p} (t : @NTerm p) := fresh_var (free_vars t).

Fixpoint free_vars_list {p} (terms : list (@NTerm p)) :=
  match terms with
    | [] => []
    | t :: ts => free_vars t ++ free_vars_list ts
  end.

Definition newvarlst {p} (ts : list (@NTerm p)) := fresh_var (free_vars_list ts).

Definition newvars {p} (n : nat) (ts : list (@NTerm p)) :=
  fresh_distinct_vars n (free_vars_list ts).

Definition newvars2 {p} (terms : list (@NTerm p)) :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
    (v1, v2).

Definition newvars3 {p} (terms : list (@NTerm p)) :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
    (v1, v2, v3).

Definition newvars4 {p} (terms : list (@NTerm p)) :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
  let v4 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3]) in
    (v1, v2, v3, v4).

Definition newvars5 {p} (terms : list (@NTerm p)) :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
  let v4 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3]) in
  let v5 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4]) in
    (v1, v2, v3, v4, v5).

Definition newvars6 {p} (terms : list (@NTerm p)) :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
  let v4 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3]) in
  let v5 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4]) in
  let v6 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4, mk_var v5]) in
    (v1, v2, v3, v4, v5, v6).

Definition newvars7 {p} (terms : list (@NTerm p)) :=
  match newvars6 terms with
    | (v1,v2,v3,v4,v5,v6) =>
      let v7 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4, mk_var v5, mk_var v6]) in
      (v1, v2, v3, v4, v5, v6, v7)
  end.


(* --- non primitives --- *)

Definition mk_id {p} : @NTerm p := mk_lam nvarx (mk_var nvarx).

Definition mk_bottom {p} : @NTerm p := mk_fix mk_id.
Definition mk_bot {p} : @NTerm p := mk_bottom.

Definition mk_vbot {p} v : @NTerm p := mk_fix (mk_lam v (mk_var v)).

Definition mk_false {p} : @NTerm p := mk_approx mk_axiom mk_bot.
Definition mk_true  {p} : @NTerm p := mk_approx mk_axiom mk_axiom.

Definition mk_void {p} : @NTerm p := mk_false.
Definition mk_unit {p} : @NTerm p  := mk_true.

Definition mk_btrue  {p} : @NTerm p := mk_inl mk_axiom.
Definition mk_bfalse {p} : @NTerm p := mk_inr mk_axiom.

Definition mk_ite {p} (a b c : @NTerm p) :=
  mk_decide a (newvar b) b (newvar c) c.

Definition mk_tt {p} : @NTerm p := mk_btrue.
Definition mk_ff {p} : @NTerm p := mk_bfalse.

Definition mk_pi1 {p} (t : @NTerm p) := mk_spread t nvarx nvary (mk_var nvarx).
Definition mk_pi2 {p} (t : @NTerm p) := mk_spread t nvarx nvary (mk_var nvary).

Definition mk_outl {p} (t : @NTerm p) := mk_decide t nvarx (mk_var nvarx) nvary mk_bot.
Definition mk_outr {p} (t : @NTerm p) := mk_decide t nvarx mk_bot nvary (mk_var nvary).

Definition mk_halts {p} (t : @NTerm p) := mk_approx mk_axiom (mk_cbv t nvarx mk_axiom).

Definition mk_uall   {p} := @mk_isect p.
Definition mk_all    {p} := @mk_function p.
Definition mk_exists {p} := @mk_product p.

Definition mk_top {p} : @NTerm p := mk_isect mk_false nvarx mk_false.

Definition mk_member {p} (t T : @NTerm p) := mk_equality t t T.

Definition mk_rmember {p} (t T : @NTerm p) := mk_requality t t T.

Definition mk_type {p} (t : @NTerm p) := mk_tequality t t.

Definition mk_bool {p} : @NTerm p := mk_union mk_unit mk_unit.

Definition mk_apply2 {p} (R x y : @NTerm p) := mk_apply (mk_apply R x) y.

Definition mk_apply3 {p} (f a b c : @NTerm p) :=
  mk_apply (mk_apply (mk_apply f a) b) c.

Definition mk_apply4 {p} (f a b c d : @NTerm p) :=
  mk_apply (mk_apply (mk_apply (mk_apply f a) b) c) d.

Definition mk_squash {p} (T : @NTerm p) := mk_image T (mk_lam nvarx mk_axiom).

Definition mk_lam3 {p} v1 v2 v3 (b : @NTerm p) := mk_lam v1 (mk_lam v2 (mk_lam v3 b)).

Definition mk_less_than {p} (a b : @NTerm p) := mk_less a b mk_true mk_false.

Definition mk_or {p} (A B : @NTerm p) := mk_union A B.

Definition mk_eor {p} (A B : @NTerm p) := mk_eunion A B.

Definition mk_zero {p} : @NTerm p := mk_nat 0.
Definition mk_one  {p} : @NTerm p := mk_nat 1.
Definition mk_two  {p} : @NTerm p := mk_nat 2.

(*
Definition mk_fun (T1 : NTerm) (T2 : NTerm) :=
  oterm (Can NFunction) [nobnd T1, bterm [v] T2].

Definition mk_product (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NProduct) [nobnd T1, bterm [v] T2].
*)



(* --- foldings --- *)

Lemma fold_integer {p} :
  forall i, oterm (Can (Nint i)) [] = @mk_integer p i.
Proof. sp. Qed.

Lemma fold_token {p} :
  forall s, oterm (Can (NTok s)) [] = @mk_token p s.
Proof. sp. Qed.

Lemma fold_utoken {p} :
  forall u, oterm (Can (NUTok u)) [] = @mk_utoken p u.
Proof. sp. Qed.

Lemma fold_atom {p} :
  oterm (Can NAtom) [] = @mk_atom p.
Proof. sp. Qed.

Lemma fold_uatom {p} :
  oterm (Can NUAtom) [] = @mk_uatom p.
Proof. sp. Qed.

Lemma fold_lam {p} :
  forall v (b : @NTerm p), oterm (Can NLambda) [bterm [v] b] = mk_lam v b.
Proof. sp. Qed.

Lemma fold_apply {p} :
  forall (a b : @NTerm p), oterm (NCan NApply) [ nobnd a, nobnd b ] = mk_apply a b.
Proof. sp. Qed.

Lemma fold_eapply {p} :
  forall (a b : @NTerm p), oterm (NCan NEApply) [ nobnd a, nobnd b ] = mk_eapply a b.
Proof. sp. Qed.

(*
Lemma fold_apseq {p} :
  forall f (a : @NTerm p), oterm (NCan (NApseq f)) [ nobnd a ] = mk_apseq f a.
Proof. sp. Qed.
*)

Lemma fold_decide {p} :
  forall (d : @NTerm p) x f y g,
    oterm (NCan NDecide) [nobnd d, bterm [x] f, bterm [y] g]
    = mk_decide d x f y g.
Proof. sp. Qed.

Lemma fold_spread {p} :
  forall (a : @NTerm p) x y b,
    oterm (NCan NSpread) [nobnd a, bterm [x,y] b]
    = mk_spread a x y b.
Proof. sp. Qed.

Lemma fold_dsup {p} :
  forall (a : @NTerm p) x y b,
    oterm (NCan NDsup) [nobnd a, bterm [x,y] b]
    = mk_dsup a x y b.
Proof. sp. Qed.

Lemma fold_approx {p} :
  forall (a b : @NTerm p), oterm (Can NApprox) [ nobnd a, nobnd b ] = mk_approx a b.
Proof. sp. Qed.

Lemma fold_cequiv {p} :
  forall (a b : @NTerm p), oterm (Can NCequiv) [ nobnd a, nobnd b ] = mk_cequiv a b.
Proof. sp. Qed.

Lemma fold_pertype {p} :
  forall (a : @NTerm p), oterm (Can NEPertype) [ nobnd a ] = mk_pertype a.
Proof. sp. Qed.

Lemma fold_ipertype {p} :
  forall (a : @NTerm p), oterm (Can NIPertype) [ nobnd a ] = mk_ipertype a.
Proof. sp. Qed.

Lemma fold_spertype {p} :
  forall (a : @NTerm p), oterm (Can NSPertype) [ nobnd a ] = mk_spertype a.
Proof. sp. Qed.

Lemma fold_tuni {p} :
  forall (a : @NTerm p), oterm (NCan NTUni) [ nobnd a ] = mk_tuni a.
Proof. sp. Qed.

Lemma fold_minus {p} :
  forall (a : @NTerm p), oterm (NCan NMinus) [ nobnd a ] = mk_minus a.
Proof. sp. Qed.

Lemma fold_admiss {p} :
  forall (a : @NTerm p), oterm (Can NAdmiss) [ nobnd a ] = mk_admiss a.
Proof. sp. Qed.

Lemma fold_mono {p} :
  forall (a : @NTerm p), oterm (Can NMono) [ nobnd a ] = mk_mono a.
Proof. sp. Qed.

Lemma fold_partial {p} :
  forall (a : @NTerm p), oterm (Can NPartial) [ nobnd a ] = mk_partial a.
Proof. sp. Qed.

(*
Lemma fold_esquash :
  forall a, oterm (Can NEsquash) [ nobnd a ] = mk_esquash a.
Proof.
  sp.
Qed.
*)

Lemma fold_compute {p} :
  forall (a b n : @NTerm p),
    oterm (Can NCompute) [ nobnd a, nobnd b, nobnd n ]
    = mk_compute a b n.
Proof. sp. Qed.

Lemma fold_equality {p} :
  forall (a b c : @NTerm p),
    oterm (Can NEquality) [ nobnd a, nobnd b, nobnd c ]
    = mk_equality a b c.
Proof. sp. Qed.

Lemma fold_requality {p} :
  forall (a b c : @NTerm p),
    oterm (Can NREquality) [ nobnd a, nobnd b, nobnd c ]
    = mk_requality a b c.
Proof. sp. Qed.

Lemma fold_free_from_atom {p} :
  forall (a b c : @NTerm p),
    oterm (Can NFreeFromAtom) [ nobnd a, nobnd b, nobnd c ]
    = mk_free_from_atom a b c.
Proof. sp. Qed.

Lemma fold_efree_from_atom {p} :
  forall (a b c : @NTerm p),
    oterm (Can NEFreeFromAtom) [ nobnd a, nobnd b, nobnd c ]
    = mk_efree_from_atom a b c.
Proof. sp. Qed.

Lemma fold_free_from_atoms {p} :
  forall (a b : @NTerm p),
    oterm (Can NFreeFromAtoms) [ nobnd a, nobnd b ]
    = mk_free_from_atoms a b.
Proof. sp. Qed.

Lemma fold_free_from_defs {p} :
  forall (A a : @NTerm p),
    oterm (Can NFreeFromDefs) [ nobnd A, nobnd a ]
    = mk_free_from_defs A a.
Proof. sp. Qed.

Lemma fold_tequality {p} :
  forall (a b : @NTerm p),
    oterm (Can NTEquality) [ nobnd a, nobnd b ]
    = mk_tequality a b.
Proof. sp. Qed.

Lemma fold_base {p} :
  oterm (Can NBase) [] = @mk_base p.
Proof. sp. Qed.

Lemma fold_member {p} :
  forall (t T : @NTerm p),
    mk_equality t t T = mk_member t T.
Proof. sp. Qed.

Lemma fold_rmember {p} :
  forall (t T : @NTerm p),
    mk_requality t t T = mk_rmember t T.
Proof. sp. Qed.

Lemma fold_mk_type {p} :
  forall (t : @NTerm p),
    mk_tequality t t = mk_type t.
Proof. sp. Qed.

Lemma fold_cbv {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (NCan NCbv) [nobnd t1, bterm [v] t2] = mk_cbv t1 v t2.
Proof. sp. Qed.

Lemma fold_try {p} :
  forall (t1 : @NTerm p) a v t2,
    oterm (NCan NTryCatch) [nobnd t1, nobnd a, bterm [v] t2] = mk_try t1 a v t2.
Proof. sp. Qed.

Lemma fold_fresh {p} :
  forall v (t : @NTerm p),
    oterm (NCan NFresh) [bterm [v] t] = mk_fresh v t.
Proof. sp. Qed.

Lemma fold_sleep {p} :
  forall (t : @NTerm p), oterm (NCan NSleep) [nobnd t] = mk_sleep t.
Proof. sp. Qed.

Lemma fold_halts {p} :
  forall (t : @NTerm p),
    mk_approx mk_axiom (mk_cbv t nvarx mk_axiom) = mk_halts t.
Proof. sp. Qed.

Lemma fold_function {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NFunction) [nobnd t1, bterm [v] t2] = mk_function t1 v t2.
Proof. sp. Qed.

Lemma fold_isect {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NIsect) [nobnd t1, bterm [v] t2] = mk_isect t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_disect {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NDIsect) [nobnd t1, bterm [v] t2] = mk_disect t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_eisect {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NEIsect) [nobnd t1, bterm [v] t2] = mk_eisect t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_w {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NW) [nobnd t1, bterm [v] t2] = mk_w t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_m {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NM) [nobnd t1, bterm [v] t2] = mk_m t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_pw {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    oterm (Can NPW)
          [nobnd P,
           bterm [ap] A,
           bterm [bp,ba] B,
           bterm [cp,ca,cb] C,
           nobnd p
          ]
    = mk_pw P ap A bp ba B cp ca cb C p.
Proof.
  sp.
Qed.

Lemma fold_pm {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    oterm (Can NPM)
          [nobnd P,
           bterm [ap] A,
           bterm [bp,ba] B,
           bterm [cp,ca,cb] C,
           nobnd p
          ]
    = mk_pm P ap A bp ba B cp ca cb C p.
Proof.
  sp.
Qed.

Lemma fold_product {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NProduct) [nobnd t1, bterm [v] t2] = mk_product t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_set {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NSet) [nobnd t1, bterm [v] t2] = mk_set t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_texc {p} :
  forall (t1 t2 : @NTerm p),
    oterm (Can NTExc) [nobnd t1, nobnd t2] = mk_texc t1 t2.
Proof.
  sp.
Qed.

Lemma fold_union {p} :
  forall (t1 : @NTerm p) t2,
    oterm (Can NUnion) [nobnd t1, nobnd t2] = mk_union t1 t2.
Proof.
  sp.
Qed.

Lemma fold_eunion {p} :
  forall (t1 : @NTerm p) t2,
    oterm (Can NEUnion) [nobnd t1, nobnd t2] = mk_eunion t1 t2.
Proof.
  sp.
Qed.

Lemma fold_union2 {p} :
  forall (t1 : @NTerm p) t2,
    oterm (Can NUnion2) [nobnd t1, nobnd t2] = mk_union2 t1 t2.
Proof.
  sp.
Qed.

Lemma fold_tunion {p} :
  forall (t1 : @NTerm p) v t2,
    oterm (Can NTUnion) [nobnd t1, bterm [v] t2] = mk_tunion t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_quotient {p} :
  forall (t1 : @NTerm p) v1 v2 t2,
    oterm (Can NQuotient) [nobnd t1, bterm [v1;v2] t2] = mk_quotient t1 v1 v2 t2.
Proof.
  sp.
Qed.

Lemma fold_pair {p} :
  forall (a b : @NTerm p), oterm (Can NPair) [ nobnd a, nobnd b ] = mk_pair a b.
Proof.
  sp.
Qed.

Lemma fold_ispair {p} :
  forall (a b c : @NTerm p),
    oterm (NCan (NCanTest CanIspair)) [ nobnd a, nobnd b, nobnd c ]
    = mk_ispair a b c.
Proof. sp. Qed.

Lemma fold_isinl {p} :
  forall (a b c : @NTerm p),
    oterm (NCan (NCanTest CanIsinl)) [ nobnd a, nobnd b, nobnd c ]
    = mk_isinl a b c.
Proof. sp. Qed.

Lemma fold_isinr {p} :
  forall (a b c : @NTerm p),
    oterm (NCan (NCanTest CanIsinr)) [ nobnd a, nobnd b, nobnd c ]
    = mk_isinr a b c.
Proof. sp. Qed.

Lemma fold_isaxiom {p} :
  forall (a b c : @NTerm p),
    oterm (NCan (NCanTest CanIsaxiom)) [ nobnd a, nobnd b, nobnd c ]
    = mk_isaxiom a b c.
Proof. sp. Qed.

Lemma fold_isint {p} :
  forall (a b c : @NTerm p),
    oterm (NCan (NCanTest CanIsint)) [ nobnd a, nobnd b, nobnd c ]
    = mk_isint a b c.
Proof. sp. Qed.

Lemma fold_islambda {p} :
  forall (a b c : @NTerm p),
    oterm (NCan (NCanTest CanIslambda)) [ nobnd a, nobnd b, nobnd c ]
    = mk_islambda a b c.
Proof. sp. Qed.

Lemma fold_sup {p} :
  forall (a b : @NTerm p), oterm (Can NSup) [ nobnd a, nobnd b ] = mk_sup a b.
Proof. sp. Qed.

Lemma fold_refl {p} :
  forall (a : @NTerm p), oterm (Can NRefl) [ nobnd a ] = mk_refl a.
Proof. sp. Qed.

Lemma fold_exception {p} :
  forall a (e : @NTerm p), oterm Exc [ nobnd a, nobnd e ] = mk_exception a e.
Proof. sp. Qed.

Lemma fold_fix {p} :
  forall (f : @NTerm p), oterm (NCan NFix) [ nobnd f ] = mk_fix f.
Proof. sp. Qed.

Lemma fold_parallel {p} :
  forall (a b : @NTerm p), oterm (NCan NParallel) [ nobnd a, nobnd b ] = mk_parallel a b.
Proof. sp. Qed.



(* ------ SIMPLE CHECKERS ON TERMS ------ *)

Definition ispair {p} (t : @NTerm p) :=
  match t with
    | (| a , b |) => true
    | _ => false
  end.

(* ------ SIMPLE OPERATORS ON TERMS ------ *)

(*
Fixpoint depth (t : NTerm) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => lsum map depth_bterm bterms
  end
 with depth_bterm (lv : list NVar) (nt : NTerm) :=
  match bt with
  | bterm lv nt => depth nt
  end.
*)



(* ------ INDUCTION ON TERMS ------ *)


(* Some of the ordinal stuff comes from

     https://github.com/martijnvermaat/infinitary-rewriting-coq/blob/master/Ordinal.v

 *)

Definition IsTypeOpid {p} (opid : @Opid p) : bool :=
  match opid with
  | Can (NUni _)   => true
  | Can NEquality  => true
  | Can NREquality => true
  | Can NTEquality => true
  | Can NInt       => true
  | Can NAtom      => true
  | Can NBase      => true
  | Can NFunction  => true
  | Can NProduct   => true
  | Can NSet       => true
  | Can NQuotient  => true
  | Can NIsect     => true
  | Can NDIsect    => true
  | Can NEIsect    => true
  | Can NW         => true
  | Can NEPertype  => true
  | Can NIPertype  => true
  | Can NSPertype  => true
  | Can NPartial   => true
  | Can NTExc      => true
  | Can NUnion     => true
  | Can NEUnion    => true
  | Can NUnion2    => true
  | Can NTUnion    => true
  | Can NApprox    => true
  | Can NCequiv    => true
  | Can NCompute   => true
  | Can NRec       => true
  | Can NImage     => true
  | _ => false
  end.

Definition IsType {p} (t : @NTerm p) : bool :=
  match t with
  | vterm _ => false
  | oterm opid _ => IsTypeOpid opid
  end.


Lemma num_bvars_on_bterm {p} :
  forall l (n : @NTerm p),
    num_bvars (bterm l n) = length l.
Proof.
  unfold num_bvars; simpl; sp.
Qed.

Definition no_vars_like {o} (t : @NTerm o) :=
  closed t # noutokens t.

Definition no_vars_like_b {o} (t : @NTerm o) : bool :=
  nullb (free_vars t) && nullb (get_utokens t).

Fixpoint wft {o} (t : @NTerm o) : obool :=
  match t with
    | vterm _ => otrue
    | oterm op bts =>
      oband (bool2obool (beq_list eq_nat_dec (map (num_bvars) bts) (OpBindings op)))
            (oball (map wftb bts))
  end
with wftb {p} (bt : BTerm) : obool :=
  match bt with
    | bterm vars t => wft t
  end.

Definition wf_term {p} (t : @NTerm p) := wft t = term2otrue t.

Lemma fold_wf_term {o} : forall t : @NTerm o, wft t = term2otrue t <=> wf_term t.
Proof. sp. Qed.

Definition wf_bterm {p} (b : @BTerm p) := wftb b = bterm2otrue b.

Lemma wf_term_proof_irrelevance {p} :
  forall (t : @NTerm p),
  forall x y : wf_term t,
    x = y.
Proof.
  intros.
  apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_term ?t , H2 : wf_term ?t |- _ ] =>
    pose proof (wf_term_proof_irrelevance t H2 H1) as h; subst
end : pi.

Definition wf_term_extract {p} :=
  fun (t : @NTerm p) (x : wf_term t) =>
    match x return (x = match x with
                          | eq_refl => eq_refl (wft t)
                        end)
    with
      | eq_refl => eq_refl eq_refl
    end.

(*
Definition wf_term_extract1 :=
  fun (t : NTerm) (x : wf_term t) =>
    match x in _ = b return match b with
                     | true => x = eq_refl (wft t)
                   end
    with
      | eq_refl => eq_refl eq_refl
    end.

Lemma wf_term_extract2 :
  forall t : NTerm,
  forall x : wf_term t,
    x = eq_refl (wft t).
*)

(*Lemma yyy : forall A (x : A) (pf : x = x), pf = eq_refl x.
Lemma xxx : forall t (x : wft t = true), x = eq_refl (wft t).*)

Lemma oball_ofalse :
  forall (l : list obool),
    oball l = ofalse -> LIn ofalse l.
Proof.
  induction l; introv h; allsimpl; ginv.
  destruct a; allsimpl; ginv.
  remember (oball l) as obl; destruct obl; ginv.
Qed.

Lemma term2otrue_not_ofalse {o} :
  forall (t : @NTerm o),
    term2otrue t = ofalse -> False.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv h; ginv.
  apply oball_ofalse in h.
  rw in_map_iff in h; exrepnd.
  destruct a as [l t].
  applydup ind in h1; tcsp.
Qed.

Lemma bterm2otrue_not_ofalse {o} :
  forall (b : @BTerm o),
    bterm2otrue b = ofalse -> False.
Proof.
  introv e.
  destruct b as [l t]; allsimpl.
  apply term2otrue_not_ofalse in e; sp.
Qed.

Lemma wft_otrue_implies_term2otrue_otrue {o} :
  forall (t : @NTerm o),
    wft t = otrue
    -> term2otrue t = otrue.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv e; ginv.
  remember (beq_list eq_nat_dec (map num_bvars bs) (OpBindings op)) as b.
  destruct b; allsimpl; ginv.
  clear Heqb.
  clear op.
  induction bs; allsimpl; ginv.
  destruct a as [l t]; allsimpl.
  autodimp IHbs hyp.
  { introv q h; apply (ind nt lv); auto. }

  remember (wft t) as ob1; symmetry in Heqob1; destruct ob1; allsimpl; ginv.

  - pose proof (ind t l) as h; repeat (autodimp h hyp).
    rw h; simpl; auto.

  - remember (oball (map wftb bs)) as ob2; symmetry in Heqob2.
    destruct ob2; allsimpl; ginv.
Qed.

Lemma oball_map_bterm2otrue_not_ofalse {o} :
  forall (bs : list (@BTerm o)),
    oball (map bterm2otrue bs) = ofalse -> False.
Proof.
  induction bs; allsimpl; introv e; ginv.
  remember (bterm2otrue a) as ob1; symmetry in Heqob1.
  destruct ob1; allsimpl; ginv.
  - apply bterm2otrue_not_ofalse in Heqob1; sp.
  - remember (oball (map bterm2otrue bs)) as ob2; symmetry in Heqob2.
    destruct ob2; allsimpl; ginv.
Qed.

Lemma oball_map_wftb_otrue_implies {o} :
  forall (bs : list (@BTerm o)),
    oball (map wftb bs) = otrue
    -> oball (map bterm2otrue bs) = otrue.
Proof.
  induction bs; allsimpl; introv e; auto.
  destruct a as [l t]; allsimpl.
  remember (wft t) as ob; symmetry in Heqob; destruct ob; allsimpl; ginv; tcsp.
  - rw @wft_otrue_implies_term2otrue_otrue; auto.
  - remember (oball (map wftb bs)) as ob2; symmetry in Heqob2.
    destruct ob2; allsimpl; ginv; tcsp.
Qed.

Lemma wft_obseq_implies_term2otrue_obseq {o} :
  forall (t : @NTerm o) (f : nat -> obool),
    wft t = obseq f
    -> {g : nat -> obool & term2otrue t = obseq g}.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv e; ginv.

  - remember (beq_list eq_nat_dec (map num_bvars bs) (OpBindings op)) as b.
    destruct b; allsimpl; ginv.
    clear Heqb.
    clear op.

    revert dependent f.
    induction bs; allsimpl; introv e; ginv.
    destruct a as [l t]; allsimpl.
    autodimp IHbs hyp.
    { introv i; apply (ind nt lv); auto. }

    remember (wft t) as ob1; symmetry in Heqob1; destruct ob1; allsimpl; ginv.

    + pose proof (IHbs f) as q; clear IHbs.
      autodimp q hyp; exrepnd.
      applydup @wft_otrue_implies_term2otrue_otrue in Heqob1; rw Heqob0; simpl.
      eexists; eauto.

    + remember (oball (map wftb bs)) as ob2; symmetry in Heqob2.
      destruct ob2; allsimpl; ginv.

      * clear IHbs.
        pose proof (ind t l) as h; clear ind; autodimp h hyp.
        pose proof (h f) as q; clear h; autodimp q hyp; exrepnd.
        rw q0; simpl.
        rw @oball_map_wftb_otrue_implies; auto.
        eexists; eauto.

      * pose proof (IHbs o1) as q; clear IHbs; autodimp q hyp; exrepnd.
        rw q0.
        pose proof (ind t l) as h; clear ind; autodimp h hyp.
        apply h in Heqob1; exrepnd; clear h.
        rw Heqob0; simpl.
        eexists; eauto.
Qed.

Lemma oband_of_obseq :
  forall s1 s2,
    oband (obseq s1) (obseq s2)
    = obseq (fun n => oband (s1 n) (s2 n)).
Proof.
  sp.
Qed.

Fixpoint isotrue (o : obool) : Prop :=
  match o with
    | otrue => True
    | ofalse => False
    | obseq f => forall n, isotrue (f n)
  end.

Lemma isotrue_oband :
  forall o1 o2, isotrue (oband o1 o2) <=> (isotrue o1 # isotrue o2).
Proof.
  induction o1 as [|?|f ind]; introv; split; intro isob; allsimpl; try dands; tcsp.
  - introv.
    destruct o2; allsimpl; tcsp.
    pose proof (isob n) as h.
    apply ind in h; sp.
  - destruct o2; allsimpl; tcsp.
    introv.
    pose proof (isob n) as h.
    apply ind in h; sp.
  - repnd.
    destruct o2; allsimpl; tcsp.
    introv.
    apply ind; dands; auto.
Qed.

Lemma isotrue_oball :
  forall l o, isotrue (oball l) -> LIn o l -> isotrue o.
Proof.
  induction l; introv ib io; allsimpl; tcsp.
  allrw @isotrue_oband; repnd.
  repndors; subst; auto.
Qed.

Lemma isotrue_oball_iff :
  forall l, isotrue (oball l) <=> (forall o, LIn o l -> isotrue o).
Proof.
  induction l; split; introv h; introv; allsimpl; tcsp.
  - intro q.
    allrw @isotrue_oband; repnd.
    repndors; subst; auto.
    rw IHl in h.
    apply h in q; auto.
  - apply isotrue_oband; dands; auto.
    apply IHl; introv i.
    apply h; sp.
Qed.

Lemma isotrue_oball_map_wftb_implies {o} :
  forall (bs : list (@BTerm o)) b,
    isotrue (oball (map wftb bs))
    -> LIn b bs
    -> isotrue (wftb b).
Proof.
  introv ibo ib.
  eapply isotrue_oball;[exact ibo|].
  rw in_map_iff.
  eexists; dands; eauto.
Qed.

Lemma isotrue_term2otrue {o} :
  forall (t : @NTerm o), isotrue (term2otrue t).
Proof.
  nterm_ind t as [v|op bs ind] Case; allsimpl; auto.
  apply isotrue_oball_iff; introv i.
  allrw in_map_iff; exrepnd; subst.
  destruct a as [l t]; allsimpl.
  eapply ind; eauto.
Qed.

Lemma isotrue_oball_map_bterm2otrue {o} :
  forall (bs : list (@BTerm o)),
    isotrue (oball (map bterm2otrue bs)).
Proof.
  introv.
  eapply isotrue_oball_iff; introv i.
  allrw in_map_iff; exrepnd; subst.
  destruct a; simpl.
  apply isotrue_term2otrue.
Qed.

Lemma isotrue_bool2obool :
  forall b, isotrue (bool2obool b) -> b = true.
Proof.
  introv h; destruct b; allsimpl; auto.
Qed.

Lemma isotrue_wft_implies_eq_term2otrue {o} :
  forall (t : @NTerm o), isotrue (wft t) -> wft t = term2otrue t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv iso; allsimpl; auto.

  - Case "oterm".
    allrw isotrue_oband; repnd.
    apply isotrue_bool2obool in iso0.
    rw iso0; simpl.
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    allrw isotrue_oball_iff.
    eapply ind; eauto.
    apply iso.
    rw in_map_iff; eexists; eauto.
Qed.

Lemma oball_map_wftb_eq_otrue_implies {o} :
  forall (bs : list (@BTerm o)) b,
    oball (map wftb bs) = oball (map bterm2otrue bs)
    -> LIn b bs
    -> wftb b = bterm2otrue b.
Proof.
  introv e i.
  pose proof (isotrue_oball_map_wftb_implies bs b) as h.
  repeat (autodimp h hyp);[rw e;apply isotrue_oball_map_bterm2otrue|].
  destruct b; allsimpl.
  apply isotrue_wft_implies_eq_term2otrue; auto.
Qed.

Lemma no_vars_like_b_true_iff {o} :
  forall (t : @NTerm o), no_vars_like_b t = true <=> (closed t # noutokens t).
Proof.
  introv; unfold no_vars_like_b, closed, noutokens.
  rw @andb_eq_true.
  allrw @assert_nullb.
  allrw @null_iff_nil; sp.
Qed.

Lemma implies_no_vars_like_b_true {o} :
  forall (t : @NTerm o),
    closed t
    -> noutokens t
    -> no_vars_like_b t = true.
Proof.
  introv cl nu.
  apply no_vars_like_b_true_iff; sp.
Qed.

Lemma nt_wf_eq {p} :
  forall (t : @NTerm p),
    nt_wf t <=> wf_term t.
Proof.
  unfold wf_term.
  nterm_ind t as [|o lbt ind] Case; simpl; intros.

  - Case "vterm".
    split; sp.

  - Case "oterm".
    split_iff SCase.

    + SCase "->"; intro w.
      inversion w as [|? ? imp e]; subst.
      allrw.
      rewrite beq_list_refl; simpl.
      f_equal.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl.
      applydup ind in i.
      applydup imp in i.
      inversion i1 as [? ? ntw]; subst; clear i1.
      apply i0 in ntw; auto.

    + SCase "<-".
      introv q.
      remember (beq_list eq_nat_dec (map num_bvars lbt) (OpBindings o)) as b.
      symmetry in Heqb.
      destruct b; allsimpl; tcsp;
      [|symmetry in q; apply oball_ofalse in q; allrw in_map_iff; exrepnd;
        destruct a; allsimpl;
        symmetry in q0; apply term2otrue_not_ofalse in q0; sp].
      constructor; tcsp.

      { introv i.
        destruct l as [l t].
        constructor.
        applydup ind in i.
        apply i0.
        eapply oball_map_wftb_eq_otrue_implies in q;[|exact i].
        allsimpl; auto. }

      apply assert_beq_list in Heqb; auto.
Qed.

Lemma nt_wf_implies {p} :
  forall (t : @NTerm p), nt_wf t -> wf_term t.
Proof.
  sp; apply nt_wf_eq; sp.
Qed.

Lemma wf_term_eq {p} :
  forall (t : @NTerm p), wf_term t <=> nt_wf t.
Proof.
  intro; generalize (nt_wf_eq t); sp.
  symm; auto.
Qed.

Lemma bt_wf_eq {p} :
  forall (bt : @BTerm p), bt_wf bt <=> wf_bterm bt.
Proof.
  sp; split; intro w.
  inversion w; subst; unfold wf_bterm; simpl.
  fold (wf_term nt).
  apply wf_term_eq; auto.
  destruct bt; allunfold (@wf_bterm p); allsimpl.
  fold (wf_term n) in w.
  constructor.
  apply nt_wf_eq; auto.
Qed.

(*
Inductive nt_wfb (t:NTerm) : bool :=
 match t with
 | vterm _ => true
 | bterm _ rt => nt_wfb rt
 | oterm o lnt : (eq map (num_bvars) lnt  OpBindings o).
*)

Definition closedb {p} (t : @NTerm p) : bool := nullb (free_vars(t)).
Definition closed_bt {p} (bt : @BTerm p) := free_vars_bterm bt = [].


(* end hide *)
Definition isprogram_bt {p} (bt : @BTerm p) := closed_bt bt # bt_wf bt.

(** Our definition [isprog] below is is logically equivalent to [isprogram],
    but unlike [isprogram], it is easy to prove that
    for any [t], all members(proofs) of [isprog t] are equal.
    An interested reader can look at the lemma
    %\coqexternalref{UIP\_dec}
    {http://coq.inria.fr/distrib/8.4pl2/stdlib/Coq.Logic.Eqdep\_dec}
    {\coqdocdefinition{UIP\_dec}}% from that standard library.
    As mentioned before, clicking on the lemma name in 
    the previous sentence should open
    the corresponding webpage of the Coq standard library.
    Instead, one can also look at the lemma [isprog_eq] below and
    safely ignore these technicalites.

*)
Definition isprog {p} (t : @NTerm p) :=
  assert (nullb (free_vars t)) # wf_term t.
(* begin hide *)

Definition isprog_bt {p} (bt : @BTerm p) :=
  assert (nullb (free_vars_bterm bt)) # wf_bterm bt.

Definition isprog_vars {p} (vs : list NVar) (t : @NTerm p) :=
  assert (sub_vars (free_vars t) vs) # wf_term t.

Lemma closed_nt {p} :
  forall (op : @Opid p) bts,
    closed (oterm op bts)
    <=>
    forall bt, LIn bt bts -> closed_bt bt.
Proof.
  sp; unfold closed, closed_bt; simpl; trw flat_map_empty; split; sp.
Qed.

Lemma closed_nt0 {p} :
  forall (o : @Opid p) nt, closed (oterm o [bterm [] nt]) -> closed nt.
Proof.
  intros. unfold closed in H. simpl in H. apply app_eq_nil in H. repnd.
  clears_last. rewrite remove_var_nil in H0. auto.
Qed.

Lemma closed_null_free_vars {p} :
  forall (t : @NTerm p),
    closed t <=> null (free_vars t).
Proof.
  unfold closed; sp.
  trw null_iff_nil; sp.
Qed.

Lemma isprog_proof_irrelevance {p} :
  forall (t : @NTerm p),
  forall x y : isprog t,
    x = y.
Proof.
  intros.
  destruct x, y.
  f_equal; apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : isprog ?t , H2 : isprog ?t |- _ ] =>
    pose proof (isprog_proof_irrelevance t H2 H1) as h; subst
end : pi.

Lemma isprog_vars_proof_irrelevance {p} :
  forall (t : @NTerm p) vs,
  forall x y : isprog_vars vs t,
    x = y.
Proof.
  intros.
  destruct x, y.
  f_equal; apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : isprog_vars ?vs ?t , H2 : isprog_vars ?vs ?t |- _ ] =>
    pose proof (isprog_vars_proof_irrelevance t vs H2 H1) as h; subst
end : pi.

Ltac irr_step :=
  match goal with
    | [ H1 : isprog ?a, H2 : isprog ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_proof_irrelevance; subst
    | [ H1 : isprog_vars ?vs ?a, H2 : isprog_vars ?vs ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_vars_proof_irrelevance; subst
  end.

Ltac irr := repeat irr_step.

Ltac abs_bool2obool n :=
  match goal with
    | [ H : context[bool2obool ?b] |- _ ] => remember b as n
  end.

Lemma assert_true_iff : assert true <=> True.
Proof.
  unfold assert; simpl; split; sp.
Qed.

Lemma assert_false_iff : assert false <=> False.
Proof.
  unfold assert; simpl; split; sp.
Qed.

Lemma isprogram_eq {p} :
  forall (t : @NTerm p),
    isprogram t <=> isprog t.
Proof.
  unfold isprog, isprogram.
  nterm_ind t as [v|op bs ind] Case; simpl; intros.

  - Case "vterm".
    rw assert_false_iff.
    rw @wf_term_eq.
    unfold closed; simpl.
    split; intro h; repnd; dands; tcsp.

  - Case "oterm".
    rw @wf_term_eq.
    rw @assert_nullb.
    allrw null_iff_nil.
    split_iff SCase; tcsp.
Qed.

Lemma isprogram_implies {p} :
  forall (t : @NTerm p), isprogram t -> isprog t.
Proof.
  sp; apply isprogram_eq; sp.
Qed.

Lemma isprog_implies {p} :
  forall t : @NTerm p, isprog t -> isprogram t.
Proof.
  sp; apply isprogram_eq; sp.
Qed.

(* end hide *)
Lemma isprog_eq {p} :
  forall (t : @NTerm p), isprog t <=> isprogram t.
Proof.
  intro; symm; apply isprogram_eq; auto.
Qed.
(* begin hide *)

Lemma isprogram_bt_eq {p} :
  forall (bt : @BTerm p),
    isprogram_bt bt <=> isprog_bt bt.
Proof.
  introv; unfold isprogram_bt, isprog_bt, closed_bt; split; intro h;
  repnd; dands; auto.

  - allrw; simpl.
    apply assert_true_iff; auto.

  - apply bt_wf_eq; auto.

  - allrw assert_nullb.
    allrw null_iff_nil; auto.

  - apply bt_wf_eq; auto.
Qed.

Lemma isprog_vars_eq {p} :
  forall (t : @NTerm p) vs,
    isprog_vars vs t <=> subvars (free_vars t) vs # nt_wf t.
Proof.
  unfold isprog_vars; sp.
  rw @nt_wf_eq; sp.
Qed.

Lemma isprog_vars_if_isprog {p} :
  forall vs (t : @NTerm p), isprog t -> isprog_vars vs t.
Proof.
  introv ip.
  rw @isprog_vars_eq.
  rw @isprog_eq in ip.
  destruct ip; sp.
  allunfold @closed; allrw; sp.
Qed.

Lemma isprog_vars_app_l {p} :
  forall (t : @NTerm p) vs1 vs2,
    isprog_vars vs2 t
    -> isprog_vars (vs1 ++ vs2) t.
Proof.
  sp; alltrewrite (@isprog_vars_eq p); sp.
  alltrewrite subvars_eq.
  apply subset_app_l; sp.
Qed.

Definition areprograms {p} (ts : list (@NTerm p)) :=
  forall t, LIn t ts -> isprogram t.

Lemma areprograms_nil {p} : @areprograms p [].
Proof.
  unfold areprograms; simpl; sp.
Qed.

Lemma areprograms_snoc {p} :
  forall (t : @NTerm p) ts,
    areprograms (snoc ts t) <=> areprograms ts # isprogram t.
Proof.
  unfold areprograms; sp; split; sp; try (apply_hyp; rw in_snoc; sp).
  alltrewrite in_snoc; sp; subst; sp.
Qed.

Lemma areprograms_cons {p} :
  forall (t : @NTerm p) ts, areprograms (t :: ts) <=> isprogram t # areprograms ts.
Proof.
  unfold areprograms; sp; simpl; split; sp; subst; sp.
Qed.

Lemma areprograms_app {p} :
  forall (ts1 ts2 : list (@NTerm p)),
    areprograms (ts1 ++ ts2) <=> areprograms ts1 # areprograms ts2.
Proof.
  unfold areprograms; sp; split; sp.
  apply_hyp; rw in_app_iff; sp.
  apply_hyp; rw in_app_iff; sp.
  alltrewrite in_app_iff; sp.
Qed.

Lemma isprogram_vterm {p} :
  forall v, @isprogram p (vterm v) <=> False.
Proof.
  unfold isprogram, closed; simpl; sp; split; sp.
Qed.

(*
Ltac repnd :=
  repeat match goal with
           | [ H : _ # _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
           | [ H : _ # _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
         end.
*)

Theorem isprogram_ot_iff {p} :
  forall (o : @Opid p) bts,
    isprogram (oterm o bts)
    <=>
    (map num_bvars bts = OpBindings o
     # forall bt, LIn bt bts -> isprogram_bt bt).
Proof.
  intros. sp_iff Case.

  - Case "->".
    intros Hisp.
    unfold isprogram in Hisp. repnd.
    inverts Hisp0 as Hflat. inverts Hisp.
    split;auto. intros bt Hin.
    unfold isprogram_bt.
    rw flat_map_empty in Hflat.
    apply_in_hyp pp; sp.

  - Case "<-".
    intros eq; destruct eq as [Hmap Hstclose].
    unfold isprogram, closed.

    split; try (constructor); auto;
    try (simpl; apply flat_map_empty);
    intros a ain;
    apply Hstclose in ain; inversion ain; sp.
Qed.

Theorem nt_wf_ot_implies {p} :
  forall lv (o : @Opid p) nt1 bts,
    nt_wf (oterm o  bts)
    -> LIn (bterm lv nt1) bts
    -> nt_wf nt1.
Proof. intros ? ? ? ? Hwf Hin. inverts Hwf as Hwf Hmap.
  assert (bt_wf (bterm lv nt1)) as Hbf by (apply Hwf; auto).
  inverts Hbf. auto.
Qed.


Lemma newvar_prop {p} :
  forall (t : @NTerm p), ! LIn (newvar t) (free_vars t).
Proof.
  unfold newvar; sp.
  allapply fresh_var_not_in; sp.
Qed.

Lemma newvar_not_in_free_vars {p} :
  forall (t : @NTerm p),
    ! LIn nvarx (free_vars t)
    -> newvar t = nvarx.
Proof.
  sp.
  unfold newvar.
  apply fresh_var_nvarx; sp.
Qed.

Lemma newvar_prog {p} :
  forall (t : @NTerm p),
    isprog t
    -> newvar t = nvarx.
Proof.
  sp.
  unfold newvar.
  apply isprog_eq in H.
  inversion H.
  unfold closed in H0.
  rewrite H0; sp.
Qed.

Definition mk_vsubtype {p} (A : @NTerm p) v B := mk_member mk_id (mk_function A v B).
Definition mk_subtype {p} (A : @NTerm p) B := mk_vsubtype A (newvar B) B.

(* non-dependent function type *)
Definition mk_fun {p} (A B : @NTerm p) := mk_function A (newvar B) B.
(* non-dependent uniform function type *)
Definition mk_ufun {p} (A B : @NTerm p) := mk_isect A (newvar B) B.
(* non-dependent extensional uniform function type *)
Definition mk_eufun {p} (A B : @NTerm p) := mk_eisect A (newvar B) B.
(* non-dependent product type *)
Definition mk_prod {p} (A B : @NTerm p) := mk_product A (newvar B) B.

Definition mk_subtype_rel {p} (A B : @NTerm p) := mk_member mk_id (mk_fun A B).

Definition mk_iff {p} (a b : @NTerm p) := mk_prod (mk_fun a b) (mk_fun b a).

Definition mk_not {p} (P : @NTerm p) := mk_fun P mk_void.

Definition mk_le {p} (a b : @NTerm p) := mk_not (mk_less_than b a).

Definition mk_tnat {p} : @NTerm p := mk_set mk_int nvary (mk_le mk_zero (mk_var nvary)).

Definition mk_nat_sub {p} n : @NTerm p :=
  mk_set mk_tnat nvarx (mk_less_than (mk_var nvarx) n).

Definition mk_dec {p} (P : @NTerm p) := mk_or P (mk_not P).

Definition mk_plus1 {p} n : @NTerm p := mk_add n mk_one.


(** A value is a program with a canonical operator *)
Inductive isvalue {p} : @NTerm p -> Type :=
  | isv_can :
      forall t,
        isprogram t
        -> iscan t
        -> isvalue t.
Hint Constructors isvalue.

Inductive isovalue {p} : @NTerm p -> Prop :=
  | isovl :
      forall t,
        nt_wf t
        -> iscan t
        -> isovalue t.
Hint Constructors isovalue.

Lemma isvalue_closed {p} :
  forall (t : @NTerm p), isvalue t -> closed t.
Proof.
  introv isv; inversion isv; allunfold @isprogram; sp.
Qed.

Lemma isvalue_program {p} :
  forall (t : @NTerm p), isvalue t -> isprogram t.
Proof.
  introv isv; inversion isv; sp.
Qed.

Lemma isvalue_mk_lam {p} :
  forall v (b : @NTerm p), isprog_vars [v] b -> isvalue (mk_lam v b).
Proof.
  intros; repeat constructor; simpl; sp; subst.
  rw @isprog_vars_eq in H; sp.
  unfold closed; simpl; rewrite app_nil_r.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
  allrw subvars_eq.
  allrw subset_singleton_r.

  unfold subset in H0; allsimpl.
  apply_in_hyp pp; sp.
  rw @isprog_vars_eq in H; sp.
Qed.

Lemma isvalue_mk_int {p} : @isvalue p mk_int.
Proof.
  repeat constructor; simpl; sp.
Qed.

Theorem isprogram_int {p} : @isprogram p mk_int.
Proof.
  repeat constructor; simpl; sp.
Qed.

Theorem isprog_int {p} : @isprog p mk_int.
Proof.
  repeat constructor.
Qed.

Theorem wf_int {p} : @wf_term p mk_int.
Proof.
  sp.
Qed.

Lemma isprogram_mk_integer {p} : forall n : Z, @isprogram p (mk_integer n).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isprog_mk_integer' {p} : forall n : Z, @isprog p (mk_integer n).
Proof.
  repeat constructor.
Qed.

Definition isprog_mk_integer {p} : forall n : Z, @isprog p (mk_integer n)
  := fun _ => (eq_refl,eq_refl).

Lemma isvalue_mk_integer {p} : forall n : Z, @isvalue p (mk_integer n).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isovalue_mk_integer {p} : forall n : Z, @isovalue p (mk_integer n).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma wf_mk_integer' {p} : forall n : Z, @wf_term p (mk_integer n).
Proof.
  sp.
Qed.

Definition wf_mk_integer {p} : forall n : Z, @wf_term p (mk_integer n)
  := fun _ => eq_refl.

Lemma isprogram_mk_nat {p} : forall n : nat, @isprogram p (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isprogram_mk_integer.
Qed.

Lemma isprog_mk_nat' {p} : forall n : nat, @isprog p (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isprog_mk_integer.
Qed.

Definition isprog_mk_nat {p} : forall n : nat, @isprog p (mk_nat n)
  := fun _ => (eq_refl,eq_refl).

Lemma isvalue_mk_nat {p} : forall n : nat, @isvalue p (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isvalue_mk_integer.
Qed.

Lemma isovalue_mk_nat {p} : forall n : nat, @isovalue p (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isovalue_mk_integer.
Qed.

Lemma wf_mk_nat' {p} : forall n : nat, @wf_term p (mk_nat n).
Proof.
  sp.
Qed.

Definition wf_mk_nat {p} : forall n : nat, @wf_term p (mk_nat n)
  := fun _ => eq_refl.

Lemma isvalue_token {p} : forall s : String.string, @isvalue p (mk_token s).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isvalue_utoken {p} : forall u : get_patom_set p, @isvalue p (mk_utoken u).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isvalue_atom {p} : @isvalue p mk_atom.
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isvalue_uatom {p} : @isvalue p mk_uatom.
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.


Lemma isprogram_mk_uni {p} : forall n : nat, @isprogram p (mk_uni n).
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma isprog_mk_uni {p} : forall n : nat, @isprog p (mk_uni n).
Proof.
  repeat constructor.
Qed.

Lemma isvalue_mk_uni {p} : forall n : nat, @isvalue p (mk_uni n).
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma wf_mk_uni {p} : forall n : nat, @wf_term p (mk_uni n).
Proof.
  sp.
Qed.

Lemma wf_mk_var {p} : forall v, @wf_term p (mk_var v).
Proof.
  sp.
Qed.

Lemma isprogram_axiom {p} : @isprogram p mk_axiom.
Proof.
  repeat constructor; simpl; sp.
Qed.

Theorem isprog_axiom {p} : @isprog p mk_axiom.
Proof.
  repeat constructor.
Qed.



Theorem isprog_bottom {p} : @isprog p mk_bottom.
Proof.
  repeat constructor.
Qed.

Lemma isprogram_bottom {p} : @isprogram p mk_bottom.
Proof.
  rw @isprogram_eq.  repeat constructor.
 
Qed.

Theorem isvalue_axiom {p} : @isvalue p mk_axiom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem wf_axiom {p} : @wf_term p mk_axiom.
Proof.
  sp.
Qed.

Theorem isprogram_base {p} : @isprogram p mk_base.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem isprog_base {p} : @isprog p mk_base.
Proof.
  repeat constructor.
Qed.

Lemma isvalue_base {p} : @isvalue p mk_base.
Proof.
  repeat constructor; simpl; sp.
Qed.

Lemma wf_base {p} : @wf_term p mk_base.
Proof.
  sp.
Qed.

Hint Immediate isvalue_mk_int.
Hint Immediate isprogram_int.
Hint Immediate isprog_int.
Hint Immediate wf_int : wf.
Hint Immediate isvalue_axiom.
Hint Immediate isprogram_axiom.
Hint Immediate isprog_axiom.
Hint Immediate isprog_bottom.
Hint Immediate isprogram_bottom.
Hint Immediate wf_axiom : wf.
Hint Immediate isvalue_base.
Hint Immediate isprogram_base.
Hint Immediate isprog_base.
Hint Immediate wf_base : wf.

Theorem wf_pertype {p} :
  forall (a : @NTerm p), wf_term a -> wf_term (mk_pertype a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Lemma isprogram_pertype {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_pertype a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_pertype_iff {p} :
  forall (a : @NTerm p), isprogram a <=> isprogram (mk_pertype a).
Proof.
  intros; split; intro i.
  apply isprogram_pertype; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  inversion w as [|o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_pertype {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_pertype a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_pertype; auto.
Qed.

Theorem wf_partial {p} :
  forall (a : @NTerm p), wf_term a -> wf_term (mk_partial a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_partial {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_partial a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_partial; sp.
Qed.

Lemma isprogram_partial_iff {p} :
  forall (a : @NTerm p), isprogram a <=> isprogram (mk_partial a).
Proof.
  intros; split; intro i.
  apply isprogram_partial; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  inversion w as [|o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_partial {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_partial a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_partial; auto.
Qed.

Theorem isprogram_admiss {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_admiss a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_partial; sp.
Qed.

Lemma isprogram_admiss_iff {p} :
  forall (a : @NTerm p), isprogram a <=> isprogram (mk_admiss a).
Proof.
  intros; split; intro i.
  apply isprogram_admiss; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [|o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_admiss {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_admiss a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_admiss; auto.
Qed.

Theorem isprogram_mono {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_mono a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_partial; sp.
Qed.

Lemma isprogram_mono_iff {p} :
  forall (a : @NTerm p), isprogram a <=> isprogram (mk_mono a).
Proof.
  intros; split; intro i.
  apply isprogram_mono; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [|o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_mono {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_mono a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_mono; auto.
Qed.

Theorem wf_ipertype {p} :
  forall (a : @NTerm p), wf_term a -> wf_term (mk_ipertype a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_ipertype {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_ipertype a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  rewrite X0; simpl.
  rewrite remove_nvars_nil_r; sp.
  apply nt_wf_eq.
  apply nt_wf_eq in X.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_ipertype_iff {p} :
  forall (a : @NTerm p), isprogram a <=> isprogram (mk_ipertype a).
Proof.
  intros; split; intro i.
  apply isprogram_ipertype; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [|o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_ipertype {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_ipertype a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_ipertype; auto.
Qed.

Theorem wf_ipertype_iff {p} :
  forall (a : @NTerm p), wf_term a <=> wf_term (mk_ipertype a).
Proof.
  intros; split; intro i.
  apply wf_ipertype; sp.
  allrw @wf_term_eq.
  inversion i as [|o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_ipertype {p} :
  forall (f : @NTerm p) vs,
    isprog_vars vs (mk_ipertype f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_ipertype_iff; split; sp.
Qed.

Theorem wf_spertype {p} :
  forall (a : @NTerm p), wf_term a -> wf_term (mk_spertype a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_spertype {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_spertype a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  rewrite X0; simpl.
  rewrite remove_nvars_nil_r; sp.
  apply nt_wf_eq.
  apply nt_wf_eq in X.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_spertype_iff {p} :
  forall (a : @NTerm p), isprogram a <=> isprogram (mk_spertype a).
Proof.
  intros; split; intro i.
  apply isprogram_spertype; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [|o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_spertype {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_spertype a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_spertype; auto.
Qed.

Theorem wf_spertype_iff {p} :
  forall (a : @NTerm p), wf_term a <=> wf_term (mk_spertype a).
Proof.
  intros; split; intro i.
  apply wf_spertype; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_spertype {p} :
  forall (f : @NTerm p) vs,
    isprog_vars vs (mk_spertype f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_spertype_iff; split; sp.
Qed.

Lemma wf_tuni {p} :
  forall (a : @NTerm p), wf_term a -> wf_term (mk_tuni a).
Proof.
  introv h.
  apply nt_wf_eq; apply nt_wf_eq in h.
  intros; inversion h; subst;
  constructor; allsimpl; sp;
  subst; auto; simpl; constructor; auto.
Qed.

Lemma isprogram_tuni {p} :
  forall (a : @NTerm p), isprogram a -> isprogram (mk_tuni a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_tuni; sp.
Qed.

Lemma isprogram_tuni_iff {p} :
  forall (a: @NTerm p), isprogram a <=> isprogram (mk_tuni a).
Proof.
  intros; split; intro i.
  apply isprogram_tuni; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_tuni {p} :
  forall (a : @NTerm p), isprog a -> isprog (mk_tuni a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_tuni; auto.
Qed.

Theorem wf_tuni_iff {p} :
  forall (a : @NTerm p), wf_term a <=> wf_term (mk_tuni a).
Proof.
  intros; split; intro i.
  apply wf_tuni; sp.
  allrw @wf_term_eq.
  inversion i as [|o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_tuni {p} :
  forall (f : @NTerm p) vs,
    isprog_vars vs (mk_tuni f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_tuni_iff; split; sp.
Qed.

(*
Theorem wf_esquash :
  forall a, wf_term a -> wf_term (mk_esquash a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_esquash :
  forall a, isprogram a -> isprogram (mk_esquash a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  rewrite X0; simpl.
  rewrite remove_nvars_nil_r; sp.
  apply nt_wf_eq.
  apply nt_wf_eq in X.
  apply wf_pertype; sp.
Qed.

Theorem isprog_esquash :
  forall a, isprog a -> isprog (mk_esquash a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_esquash; auto.
Qed.
*)

Theorem wf_image {p} :
  forall (a b : @NTerm p), wf_term a -> wf_term b -> wf_term (mk_image a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_image_iff {p} :
  forall (a b : @NTerm p), (wf_term a # wf_term b) <=> wf_term (mk_image a b).
Proof.
  intros; split; intro k.
  apply wf_image; sp.
  allrw <- @nt_wf_eq.
  inversion k as [|i j u w]; subst; allsimpl.
  generalize (u (nobnd a)) (u (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  inversion i1; subst; inversion i2; subst; sp.
Qed.

Lemma isprogram_image {p} :
  forall (a b : @NTerm p), isprogram a -> isprogram b -> isprogram (mk_image a b).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw @nt_wf_eq.
  apply wf_image; sp.
Qed.

Lemma isprogram_image_iff {p} :
  forall (a b : @NTerm p), (isprogram a # isprogram b) <=> isprogram (mk_image a b).
Proof.
  sp; split; intro k; try (apply isprogram_image; sp).
  inversion k as [c w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repd.
  unfold isprogram, closed; allrw.
  inversion w as [|o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)) (i (nobnd b)); intros e1 e2.
  dest_imp e1 hyp.
  dest_imp e2 hyp.
  inversion e1; subst.
  inversion e2; subst; sp.
Qed.

Theorem isprog_image {p} :
  forall (a b : @NTerm p), isprog a -> isprog b -> isprog (mk_image a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_image; auto.
Qed.

Theorem wf_apply {p} :
  forall (a b : @NTerm p), wf_term a -> wf_term b -> wf_term (mk_apply a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_apply {p} :
  forall (a b : @NTerm p), isprogram a -> isprogram b -> isprogram (mk_apply a b).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw @nt_wf_eq.
  apply wf_apply; sp.
Qed.

Lemma isprogram_apply_iff {p} :
  forall (a b : @NTerm p), (isprogram a # isprogram b) <=> isprogram (mk_apply a b).
Proof.
  sp; split; intro k; try (apply isprogram_apply; sp).
  inversion k as [c w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repd.
  unfold isprogram, closed; allrw.
  inversion w as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)) (i (nobnd b)); intros e1 e2.
  dest_imp e1 hyp.
  dest_imp e2 hyp.
  inversion e1; subst.
  inversion e2; subst; sp.
Qed.

Theorem isprog_apply {p} :
  forall (a b : @NTerm p), isprog a -> isprog b -> isprog (mk_apply a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_apply; auto.
Qed.

Theorem wf_apply2 {p} :
  forall (f a b : @NTerm p),
    wf_term f -> wf_term a -> wf_term b -> wf_term (mk_apply2 f a b).
Proof.
  unfold mk_apply2; sp.
  repeat (apply wf_apply); auto.
Qed.

Theorem isprogram_apply2 {p} :
  forall (f a b : @NTerm p),
    isprogram f -> isprogram a -> isprogram b -> isprogram (mk_apply2 f a b).
Proof.
  unfold mk_apply2; sp.
  repeat (apply isprogram_apply); auto.
Qed.

Theorem isprog_apply2 {p} :
  forall (f a b : @NTerm p),
    isprog f -> isprog a -> isprog b -> isprog (mk_apply2 f a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_apply2; auto.
Qed.


Theorem wf_eapply {p} :
  forall (a b : @NTerm p), wf_term a -> wf_term b -> wf_term (mk_eapply a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_eapply {p} :
  forall (a b : @NTerm p), isprogram a -> isprogram b -> isprogram (mk_eapply a b).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw @nt_wf_eq.
  apply wf_eapply; sp.
Qed.

Lemma isprogram_eapply_iff {p} :
  forall (a b : @NTerm p), (isprogram a # isprogram b) <=> isprogram (mk_eapply a b).
Proof.
  sp; split; intro k; try (apply isprogram_eapply; sp).
  inversion k as [c w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repd.
  unfold isprogram, closed; allrw.
  inversion w as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)) (i (nobnd b)); intros e1 e2.
  dest_imp e1 hyp.
  dest_imp e2 hyp.
  inversion e1; subst.
  inversion e2; subst; sp.
Qed.

Theorem isprog_eapply {p} :
  forall (a b : @NTerm p), isprog a -> isprog b -> isprog (mk_eapply a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_eapply; auto.
Qed.


(*
Lemma wf_apseq {p} :
  forall f (a : @NTerm p), wf_term a -> wf_term (mk_apseq f a).
Proof.
  introv w; allrw <- @nt_wf_eq.
  constructor; simpl; tcsp; introv k; sp; subst; constructor; auto.
Qed.

Lemma isprogram_apseq {p} :
  forall f (a : @NTerm p), isprogram a -> isprogram (mk_apseq f a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw @nt_wf_eq.
  apply wf_apseq; sp.
Qed.

Lemma isprogram_apseq_iff {p} :
  forall f (a : @NTerm p), isprogram a <=> isprogram (mk_apseq f a).
Proof.
  sp; split; intro k; try (apply isprogram_apseq; sp).
  inversion k as [c w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repd.
  unfold isprogram, closed; allrw.
  inversion w as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)); intros e1.
  dest_imp e1 hyp.
  inversion e1; subst; sp.
Qed.

Lemma isprog_apseq {p} :
  forall f (a : @NTerm p), isprog a -> isprog (mk_apseq f a).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_apseq; auto.
Qed.
*)

(**useful for rewriting in complicated formulae*)
Theorem bt_wf_iff {p} :
  forall lv (nt : @NTerm p),
    bt_wf (bterm lv nt)
    <=> nt_wf nt.
Proof. sp_iff Case; introv H.
  Case "->". inverts H as Hwf;  auto.
  Case "<-".  constructor; auto.
Qed.

Theorem wf_parallel {p} :
  forall (a b : @NTerm p),
    wf_term a
    -> wf_term b
    -> wf_term (mk_parallel a b).
Proof.
  introv wa wb.
  repeat (rw <- @nt_wf_eq).
  constructor; allsimpl.
  - introv i; repndors; tcsp; subst; allrw @bt_wf_iff; allrw @nt_wf_eq; auto.
  - unfold num_bvars; simpl; auto.
Qed.

Lemma isprogram_parallel {p} :
  forall (a b : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram (mk_parallel a b).
Proof.
  introv pa pb.
  destruct pa as [ca wa].
  destruct pb as [cb wb].
  constructor.
  - unfold closed; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
    rw ca; rw cb; auto.
  - rw @nt_wf_eq; apply wf_parallel; rw <- @nt_wf_eq; auto.
Qed.

Lemma isprogram_parallel_iff {p} :
  forall (a b : @NTerm p),
    isprogram (mk_parallel a b) <=> (isprogram a # isprogram b).
Proof.
  introv; split; intro k; try (apply isprogram_parallel; sp).
  inversion k as [c w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  apply app_eq_nil_iff in c; repnd.
  unfold isprogram; unfold closed; rw c0; rw c.
  inversion w as [| o lnt i meq ]; subst; allsimpl; clear w.
  pose proof (i (nobnd a)) as h1; pose proof (i (nobnd b)) as h2.
  autodimp h1 hyp; autodimp h2 hyp.
  allrw @bt_wf_iff.
  dands; auto.
Qed.

Theorem isprog_parallel {p} :
  forall (a b  : @NTerm p),
    isprog a
    -> isprog b
    -> isprog (mk_parallel a b).
Proof.
  introv pa pb; allrw @isprog_eq.
  apply isprogram_parallel; auto.
Qed.

Theorem closed_approx {p} :
  forall (a b : @NTerm p), closed a -> closed b -> closed (mk_approx a b).
Proof.
  intros.
  allunfold @closed; unfold mk_approx; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_cequiv {p} :
  forall (a b : @NTerm p), closed a -> closed b -> closed (mk_cequiv a b).
Proof.
  intros.
  allunfold @closed; unfold mk_cequiv; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_texc {p} :
  forall (a b : @NTerm p),
    closed a -> closed b -> closed (mk_texc a b).
Proof.
  intros.
  allunfold @closed; unfold mk_texc; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_union {p} :
  forall (a b : @NTerm p), closed a -> closed b -> closed (mk_union a b).
Proof.
  intros.
  allunfold @closed; unfold mk_union; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_eunion {p} :
  forall (a b : @NTerm p), closed a -> closed b -> closed (mk_eunion a b).
Proof.
  intros.
  allunfold @closed; unfold mk_eunion; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_union2 {p} :
  forall (a b : @NTerm p), closed a -> closed b -> closed (mk_union2 a b).
Proof.
  intros.
  allunfold @closed; unfold mk_union2; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_compute {p} :
  forall (a b n : @NTerm p),
    closed a -> closed b -> closed n -> closed (mk_compute a b n).
Proof.
  intros.
  allunfold @closed; unfold mk_compute; simpl.
  allrw; simpl; sp.
Qed.

Theorem wf_approx {p} :
  forall (a b : @NTerm p), wf_term a -> wf_term b -> wf_term (mk_approx a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_approx_iff {p} :
  forall (a b : @NTerm p), (wf_term a # wf_term b) <=> wf_term (mk_approx a b).
Proof.
  sp; split; intros k.
  apply wf_approx; sp.
  allrw @wf_term_eq.
  inversion k as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)); generalize (i (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  inversion i1; inversion i2; sp.
Qed.

Lemma isprogram_isinl {p} :
  forall (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_isinl a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_isinl_iff {p} :
  forall (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_isinl a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_isinl; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_isinl {p} :
  forall (a b c : @NTerm p),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_isinl a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_isinl; auto.
Qed.

Lemma isprogram_isinr {p} :
  forall (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_isinr a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_isinr_iff {p} :
  forall (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_isinr a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_isinr; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_isinr {p} :
  forall (a b c : @NTerm p),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_isinr a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_isinr; auto.
Qed.

Lemma isprogram_isaxiom {p} :
  forall (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_isaxiom a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_isaxiom_iff {p} :
  forall (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_isaxiom a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_isaxiom; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_isaxiom {p} :
  forall (a b c : @NTerm p),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_isaxiom a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_isaxiom; auto.
Qed.

Lemma isprogram_islambda {p} :
  forall (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_islambda a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_islambda_iff {p} :
  forall (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_islambda a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_islambda; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_islambda {p} :
  forall (a b c : @NTerm p),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_islambda a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_islambda; auto.
Qed.


Lemma isprogram_can_test {p} :
  forall test (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_can_test test a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_ispair {p} :
  forall (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_ispair a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.
Lemma isprogram_can_test_iff {p} :
  forall test (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_can_test test a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_can_test; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_can_test {p} :
  forall test (a b c : @NTerm p),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_can_test test a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_can_test; auto.
Qed.

Lemma isprogram_ispair_iff {p} :
  forall (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_ispair a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_ispair; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_ispair {p} :
  forall (a b c : @NTerm p),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_ispair a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_ispair; auto.
Qed.

Lemma isprogram_approx {p} :
  forall (a b : @NTerm p),
    isprogram a -> isprogram b -> isprogram (mk_approx a b).
Proof.
  intros. allunfold @isprogram. repnd. split. apply closed_approx; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Lemma isprogram_approx_iff {p} :
  forall (a b : @NTerm p), (isprogram a # isprogram b) <=> isprogram (mk_approx a b).
Proof.
  intros; split; intro i.
  apply isprogram_approx; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Theorem isprog_approx {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_approx a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_approx; auto.
Qed.

Theorem wf_cequiv {p} :
  forall a b : @NTerm p, wf_term a -> wf_term b -> wf_term (mk_cequiv a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem isprogram_cequiv {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isprogram (mk_cequiv a b).
Proof.
  intros. allunfold @isprogram. repnd. split. apply closed_cequiv; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Lemma isprogram_cequiv_iff {p} :
  forall a b : @NTerm p, (isprogram a # isprogram b) <=> isprogram (mk_cequiv a b).
Proof.
  intros; split; intro i.
  apply isprogram_cequiv; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Theorem isprog_cequiv {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_cequiv a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_cequiv; auto.
Qed.

Theorem isprogram_texc {p} :
  forall a b : @NTerm p,
    isprogram a -> isprogram b -> isprogram (mk_texc a b).
Proof.
  intros. allunfold @isprogram. repnd. split. apply closed_texc; auto.
  constructor; auto. intros ? Hin.
  allsimpl; repndors; tcsp; subst;
  try (constructor;auto).
Qed.

Theorem isprog_texc {p} :
  forall a b : @NTerm p,
    isprog a -> isprog b -> isprog (mk_texc a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_texc; auto.
Qed.

Theorem isprogram_union {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isprogram (mk_union a b).
Proof.
  intros. allunfold @isprogram. repnd. split. apply closed_union; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Theorem isprog_union {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_union a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_union; auto.
Qed.

Theorem isprogram_eunion {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isprogram (mk_eunion a b).
Proof.
  intros. allunfold @isprogram. repnd. split. apply closed_eunion; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Theorem isprog_eunion {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_eunion a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_eunion; auto.
Qed.

Theorem isprogram_union2 {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isprogram (mk_union2 a b).
Proof.
  intros. allunfold @isprogram. repnd. split. apply closed_union2; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Theorem isprog_union2 {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_union2 a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_union2; auto.
Qed.

Theorem isprogram_compute {p} :
  forall a b n : @NTerm p,
    isprogram a -> isprogram b -> isprogram n -> isprogram (mk_compute a b n).
Proof.
  unfold isprogram, closed; sp; simpl; allrw; allsimpl; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Theorem isprog_compute {p} :
  forall a b n : @NTerm p,
    isprog a -> isprog b -> isprog n -> isprog (mk_compute a b n).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_compute; auto.
Qed.

Theorem isvalue_approx {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isvalue (mk_approx a b).
Proof.
 intros; constructor; simpl; auto.
 fold (mk_approx a b).
 apply isprogram_approx; auto.
Qed.

Theorem isovalue_approx {p} :
  forall a b : @NTerm p, nt_wf a -> nt_wf b -> isovalue (mk_approx a b).
Proof.
 intros; constructor; simpl; auto.
 fold (mk_approx a b).
 allrw @nt_wf_eq.
 apply wf_approx; auto.
Qed.

Theorem isvalue_cequiv {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isvalue (mk_cequiv a b).
Proof.
 intros; constructor; simpl; auto.
 apply isprogram_cequiv; auto.
Qed.

Theorem isovalue_cequiv {p} :
  forall a b : @NTerm p, nt_wf a -> nt_wf b -> isovalue (mk_cequiv a b).
Proof.
 intros; constructor; simpl; auto.
 allrw @nt_wf_eq.
 apply wf_approx; auto.
Qed.

Theorem isvalue_texc {p} :
  forall a b : @NTerm p,
    isprogram a -> isprogram b -> isvalue (mk_texc a b).
Proof.
 intros; constructor; simpl; auto.
 apply isprogram_texc; auto.
Qed.

Theorem isvalue_union {p} :
  forall a b :@NTerm p, isprogram a -> isprogram b -> isvalue (mk_union a b).
Proof.
 intros; constructor; simpl; auto.
 apply isprogram_union; auto.
Qed.

Theorem isvalue_eunion {p} :
  forall a b :@NTerm p, isprogram a -> isprogram b -> isvalue (mk_eunion a b).
Proof.
 intros; constructor; simpl; auto.
 apply isprogram_eunion; auto.
Qed.

Theorem isvalue_union2 {p} :
  forall a b :@NTerm p, isprogram a -> isprogram b -> isvalue (mk_union2 a b).
Proof.
 intros; constructor; simpl; auto.
 apply isprogram_union2; auto.
Qed.

Theorem isvalue_image {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isvalue (mk_image a b).
Proof.
  intros; constructor; simpl; auto; apply isprogram_image; auto.
Qed.

Theorem isvalue_pertype {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_pertype a).
Proof.
 intros; constructor; simpl; auto; apply isprogram_pertype; auto.
Qed.

Theorem isvalue_partial {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_partial a).
Proof.
 intros; constructor; simpl; auto; apply isprogram_partial; auto.
Qed.

Theorem isvalue_ipertype {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_ipertype a).
Proof.
  intros; constructor; simpl; auto.
  fold (mk_ipertype a).
  apply isprogram_ipertype; auto.
Qed.

Theorem isvalue_spertype {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_spertype a).
Proof.
  intros; constructor; simpl; auto.
  fold (mk_spertype a).
  apply isprogram_spertype; auto.
Qed.

(*
Theorem isvalue_tuni :
  forall a, isprogram a -> isvalue (mk_tuni a).
Proof.
 intros; constructor; apply isprogram_tuni; auto.
Qed.
*)

(*
Theorem isvalue_esquash :
  forall a, isprogram a -> isvalue (mk_esquash a).
Proof.
 intros. constructor. fold (mk_esquash a).
 apply isprogram_esquash; auto.
Qed.
*)


Lemma wf_free_from_atom {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_free_from_atom a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_efree_from_atom {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_efree_from_atom a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_free_from_atoms {p} :
  forall T t : @NTerm p,
    wf_term T -> wf_term t -> wf_term (mk_free_from_atoms T t).
Proof.
  introv wT wt; allrw <- @nt_wf_eq.
  inversion wT; inversion wt; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_free_from_defs {p} :
  forall (T t : @NTerm p),
    wf_term T -> wf_term t -> wf_term (mk_free_from_defs T t).
Proof.
  introv wT wt; allrw <- @nt_wf_eq.
  inversion wT; inversion wt; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma oball_map_wftb_eq_otrue_implies_wf_term {o} :
  forall (bs : list (@BTerm o)) t,
    oball (map wftb bs) = oball (map bterm2otrue bs)
    -> LIn (nobnd t) bs
    -> wf_term t.
Proof.
  introv e i.
  eapply oball_map_wftb_eq_otrue_implies in e;[|exact i].
  allsimpl; auto.
Qed.

Lemma wf_free_from_atom_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_free_from_atom a b T).
Proof.
  sp; split; introv h; repnd.
  - apply wf_free_from_atom; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_free_from_atom_iff2 {p} :
  forall a b T : @NTerm p,
    wf_term (mk_free_from_atom a b T) <=> (wf_term a # wf_term b # wf_term T).
Proof.
  intros; rw @wf_free_from_atom_iff; sp.
Qed.

Lemma wf_efree_from_atom_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_efree_from_atom a b T).
Proof.
  sp; split; introv h; repnd.
  - apply wf_efree_from_atom; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_efree_from_atom_iff2 {p} :
  forall a b T : @NTerm p,
    wf_term (mk_efree_from_atom a b T) <=> (wf_term a # wf_term b # wf_term T).
Proof.
  intros; rw @wf_efree_from_atom_iff; sp.
Qed.

Lemma wf_free_from_atoms_iff {p} :
  forall T t : @NTerm p,
    (wf_term T # wf_term t) <=> wf_term (mk_free_from_atoms T t).
Proof.
  sp; split; introv h; repnd.
  - apply wf_free_from_atoms; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_free_from_atoms_iff2 {p} :
  forall T t : @NTerm p,
    wf_term (mk_free_from_atoms T t) <=> (wf_term T # wf_term t).
Proof.
  intros; rw @wf_free_from_atoms_iff; sp.
Qed.

Lemma wf_free_from_defs_iff {p} :
  forall T t : @NTerm p,
    (wf_term T # wf_term t) <=> wf_term (mk_free_from_defs T t).
Proof.
  sp; split; introv h; repnd.
  - apply wf_free_from_defs; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_free_from_defs_iff2 {p} :
  forall T t : @NTerm p,
    wf_term (mk_free_from_defs T t) <=> (wf_term T # wf_term t).
Proof.
  intros; rw <- @wf_free_from_defs_iff; sp.
Qed.


Lemma wf_equality {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_equality a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_equality_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_equality a b T).
Proof.
  sp; split; introv h; repnd.
  - apply wf_equality; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_equality_iff2 {p} :
  forall a b T : @NTerm p,
    wf_term (mk_equality a b T) <=> (wf_term a # wf_term b # wf_term T).
Proof.
  intros; rw @wf_equality_iff; sp.
Qed.

Lemma wf_member {p} :
  forall a T : @NTerm p,
    wf_term a -> wf_term T -> wf_term (mk_member a T).
Proof.
  sp; unfold mk_member; apply wf_equality; sp.
Qed.

Lemma wf_member_iff {p} :
  forall a T : @NTerm p, (wf_term a # wf_term T) <=> wf_term (mk_member a T).
Proof.
  sp; split; intro i.
  apply wf_member; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd T)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_member_iff2 {p} :
  forall a T : @NTerm p, wf_term (mk_member a T) <=> (wf_term a # wf_term T).
Proof.
  intros; rw @wf_member_iff; sp.
Qed.

Lemma wf_requality {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_requality a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_requality_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_requality a b T).
Proof.
  sp; split; introv h; repnd.
  - apply wf_equality; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_requality_iff2 {p} :
  forall a b T : @NTerm p,
    wf_term (mk_requality a b T) <=> (wf_term a # wf_term b # wf_term T).
Proof.
  intros; rw @wf_requality_iff; sp.
Qed.

Lemma wf_rmember {p} :
  forall a T : @NTerm p,
    wf_term a -> wf_term T -> wf_term (mk_rmember a T).
Proof.
  sp; unfold mk_member; apply wf_requality; sp.
Qed.

Lemma wf_rmember_iff {p} :
  forall a T : @NTerm p, (wf_term a # wf_term T) <=> wf_term (mk_rmember a T).
Proof.
  sp; split; intro i.
  { apply wf_rmember; sp. }
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd T)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_rmember_iff2 {p} :
  forall a T : @NTerm p, wf_term (mk_rmember a T) <=> (wf_term a # wf_term T).
Proof.
  intros; rw @wf_rmember_iff; sp.
Qed.

Lemma wf_tequality {p} :
  forall a b : @NTerm p, wf_term a -> wf_term b -> wf_term (mk_tequality a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_tequality_iff {p} :
  forall a b : @NTerm p, (wf_term a # wf_term b) <=> wf_term (mk_tequality a b).
Proof.
  sp; split; intro h.
  - apply wf_tequality; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term;try (exact h); simpl; sp.
Qed.

Lemma wf_tequality_iff2 {p} :
  forall a b : @NTerm p, wf_term (mk_tequality a b) <=> (wf_term a # wf_term b).
Proof.
  intros; rw @wf_tequality_iff; sp.
Qed.

Lemma wf_type {p} :
  forall a : @NTerm p, wf_term a -> wf_term (mk_type a).
Proof.
  sp; apply wf_tequality; sp.
Qed.

Lemma wf_type_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_type a).
Proof.
  sp; split; intro i.
  apply wf_type; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  inversion i1; subst; sp.
Qed.

Lemma wf_type_iff2 {p} :
  forall a : @NTerm p, wf_term (mk_type a) <=> wf_term a.
Proof.
  intros; rw <- @wf_type_iff; sp.
Qed.

Lemma wf_lam {p} :
  forall v (b : @NTerm p), wf_term b -> wf_term (mk_lam v b).
Proof.
  intros v b; repeat (rw <- @nt_wf_eq).
  intros ntb; inversion ntb; subst; constructor; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma wf_lam_iff {p} :
  forall v (b : @NTerm p), (wf_term b) <=> wf_term (mk_lam v b).
Proof.
  sp; split; intro i; try (apply wf_lam; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (bterm [v] b)); intros j.
  dest_imp j hyp; sp.
  inversion j; subst; sp.
Qed.

Lemma wf_id {p} : @wf_term p mk_id.
Proof.
  apply wf_lam; sp.
Qed.
Hint Immediate wf_id : wf.

Lemma wf_squash {p} :
  forall T : @NTerm p, wf_term (mk_squash T) <=> wf_term T.
Proof.
  intro; unfold mk_squash; rw <- @wf_image_iff.
  rw <- @wf_lam_iff; split; sp.
Qed.

Theorem wf_function {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_function a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_function_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_function a v b).
Proof.
  sp; split; intro i; try (apply wf_function; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_subtype {p} :
  forall a b : @NTerm p, wf_term a -> wf_term b -> wf_term (mk_subtype a b).
Proof.
  sp; unfold mk_subtype, mk_vsubtype.
  apply wf_member; sp.
  apply wf_function; sp.
Qed.

Lemma wf_subtype_iff {p} :
  forall a b : @NTerm p, (wf_term a # wf_term b) <=> wf_term (mk_subtype a b).
Proof.
  sp; split; intro.
  apply wf_subtype; sp.
  unfold mk_subtype, mk_vsubtype in H.
  allrw <- @wf_member_iff; repd.
  allrw <- @wf_function_iff; sp.
Qed.

Lemma wf_halts {p} :
  forall a : @NTerm p, wf_term a -> wf_term (mk_halts a).
Proof.
  sp; unfold mk_halts.
  allrw @wf_term_eq.
  constructor; repeat (allsimpl; sp; subst; repeat constructor).
Qed.

Lemma wf_halts_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_halts a).
Proof.
  sp; split; intro i.
  apply wf_halts; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst.
  generalize (k (nobnd (mk_cbv a nvarx mk_axiom))); allsimpl; intro j.
  dest_imp j hyp.
  inversion j as [ lnv nt u ]; subst.
  inversion u as [| o lnt pp q ]; subst; allsimpl.
  generalize (pp (nobnd a)); intro r.
  dest_imp r hyp.
  inversion r; subst; sp.
Qed.

Lemma isprogram_free_from_atom {p} :
  forall a b T : @NTerm p,
    isprogram a
    -> isprogram b
    -> isprogram T
    -> isprogram (mk_free_from_atom a b T).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_free_from_atom_iff {p} :
  forall a b c : @NTerm p,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_free_from_atom a b c).
Proof.
  intros; split; intro i.
  apply isprogram_free_from_atom; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_free_from_atom {p} :
  forall a b T : @NTerm p,
    isprog a
    -> isprog b
    -> isprog T
    -> isprog (mk_free_from_atom a b T).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_free_from_atom; auto.
Qed.

Lemma isvalue_free_from_atom {p} :
  forall a b T : @NTerm p,
    isprogram (mk_free_from_atom a b T) -> isvalue (mk_free_from_atom a b T).
Proof. sp; constructor; sp.
Qed.

Lemma isprogram_efree_from_atom {p} :
  forall a b T : @NTerm p,
    isprogram a
    -> isprogram b
    -> isprogram T
    -> isprogram (mk_efree_from_atom a b T).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_efree_from_atom_iff {p} :
  forall a b c : @NTerm p,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_efree_from_atom a b c).
Proof.
  intros; split; intro i.
  apply isprogram_efree_from_atom; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_efree_from_atom {p} :
  forall a b T : @NTerm p,
    isprog a
    -> isprog b
    -> isprog T
    -> isprog (mk_efree_from_atom a b T).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_efree_from_atom; auto.
Qed.

Lemma isvalue_efree_from_atom {p} :
  forall a b T : @NTerm p,
    isprogram (mk_efree_from_atom a b T) -> isvalue (mk_efree_from_atom a b T).
Proof. sp; constructor; sp.
Qed.

Lemma isprogram_free_from_atoms {p} :
  forall T t : @NTerm p,
    isprogram T
    -> isprogram t
    -> isprogram (mk_free_from_atoms T t).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_free_from_atoms_iff {p} :
  forall a b : @NTerm p,
    (isprogram a # isprogram b) <=> isprogram (mk_free_from_atoms a b).
Proof.
  intros; split; intro i.
  apply isprogram_free_from_atoms; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_free_from_atoms {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_free_from_atoms a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_free_from_atoms; auto.
Qed.

Lemma isvalue_free_from_atoms {p} :
  forall a b : @NTerm p,
    isprogram (mk_free_from_atoms a b) -> isvalue (mk_free_from_atoms a b).
Proof. sp; constructor; sp.
Qed.

Lemma isprogram_free_from_defs {p} :
  forall T t : @NTerm p,
    isprogram T
    -> isprogram t
    -> isprogram (mk_free_from_defs T t).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_free_from_defs_iff {p} :
  forall a b : @NTerm p,
    (isprogram a # isprogram b) <=> isprogram (mk_free_from_defs a b).
Proof.
  intros; split; intro i.
  apply isprogram_free_from_defs; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_free_from_defs {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_free_from_defs a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_free_from_defs; auto.
Qed.

Lemma isvalue_free_from_defs {p} :
  forall a b : @NTerm p,
    isprogram (mk_free_from_defs a b) -> isvalue (mk_free_from_defs a b).
Proof. sp; constructor; sp.
Qed.

Lemma isprogram_equality {p} :
  forall a b T : @NTerm p,
    isprogram a
    -> isprogram b
    -> isprogram T
    -> isprogram (mk_equality a b T).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_equality_iff {p} :
  forall a b c : @NTerm p,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_equality a b c).
Proof.
  intros; split; intro i.
  apply isprogram_equality; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_equality {p} :
  forall a b T : @NTerm p,
    isprog a
    -> isprog b
    -> isprog T
    -> isprog (mk_equality a b T).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_equality; auto.
Qed.

Lemma isvalue_equality {p} :
  forall a b T : @NTerm p,
    isprogram (mk_equality a b T) -> isvalue (mk_equality a b T).
Proof.
 intros; constructor; simpl; auto.
Qed.

Lemma isprogram_member {p} :
  forall t T : @NTerm p,
    isprogram t
    -> isprogram T
    -> isprogram (mk_member t T).
Proof.
  unfold mk_member; sp.
  apply isprogram_equality; sp.
Qed.

Lemma isprog_member {p} :
  forall t T : @NTerm p,
    isprog t
    -> isprog T
    -> isprog (mk_member t T).
Proof.
  unfold mk_member; sp; apply isprog_equality; sp.
Qed.

Lemma isprogram_requality {p} :
  forall a b T : @NTerm p,
    isprogram a
    -> isprogram b
    -> isprogram T
    -> isprogram (mk_requality a b T).
Proof.
  repeat constructor.
  { unfold closed; simpl.
    allrw <- null_iff_nil.
    repeat (rw null_app).
    repeat (rw null_iff_nil).
    allunfold @isprogram; allunfold @closed.
    repeat (rewrite remove_nvars_nil_l); sp. }

  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_requality_iff {p} :
  forall a b c : @NTerm p,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_requality a b c).
Proof.
  intros; split; intro i.
  apply isprogram_requality; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_requality {p} :
  forall a b T : @NTerm p,
    isprog a
    -> isprog b
    -> isprog T
    -> isprog (mk_requality a b T).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_requality; auto.
Qed.

Lemma isvalue_requality {p} :
  forall a b T : @NTerm p,
    isprogram (mk_requality a b T) -> isvalue (mk_requality a b T).
Proof.
 intros; constructor; simpl; auto.
Qed.

Lemma isprogram_rmember {p} :
  forall t T : @NTerm p,
    isprogram t
    -> isprogram T
    -> isprogram (mk_rmember t T).
Proof.
  unfold mk_rmember; sp.
  apply isprogram_requality; sp.
Qed.

Lemma isprog_rmember {p} :
  forall t T : @NTerm p,
    isprog t
    -> isprog T
    -> isprog (mk_rmember t T).
Proof.
  unfold mk_rmember; sp; apply isprog_requality; sp.
Qed.

Lemma isprogram_tequality {p} :
  forall a b : @NTerm p,
    isprogram a
    -> isprogram b
    -> isprogram (mk_tequality a b).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_tequality_iff {p} :
  forall a b : @NTerm p,
    (isprogram a # isprogram b) <=> isprogram (mk_tequality a b).
Proof.
  intros; split; intro i.
  apply isprogram_tequality; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_tequality {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_tequality a b).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_tequality; auto.
Qed.

Lemma isvalue_tequality {p} :
  forall a b : @NTerm p, isprogram (mk_tequality a b) -> isvalue (mk_tequality a b).
Proof.
 intros; constructor; simpl; auto.
Qed.

Lemma isprogram_type {p} :
  forall t : @NTerm p, isprogram t -> isprogram (mk_type t).
Proof.
  unfold mk_type; sp.
  apply isprogram_tequality; sp.
Qed.

Lemma isprog_type {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_type t).
Proof.
  unfold mk_type; sp; apply isprog_tequality; sp.
Qed.

Lemma isprogram_cbv {p} :
  forall (a : @NTerm p) v b,
    isprogram a
    -> subvars (free_vars b) [v]
    -> nt_wf b
    -> isprogram (mk_cbv a v b).
Proof.
  sp.
  repeat constructor; sp.
  unfold closed; simpl.
  rw remove_nvars_nil_l.
  rewrite app_nil_r.
  rw app_eq_nil_iff; sp.
  allunfold @isprogram; allunfold @closed; sp.
  allrw subvars_eq.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
  allsimpl; sp; subst.
  constructor; allunfold @isprogram; sp.
  constructor; sp.
Qed.

Lemma isprogram_cbv_iff {p} :
  forall (a : @NTerm p) v b,
    isprogram (mk_cbv a v b)
    <=> isprogram a
        # subvars (free_vars b) [v]
        # nt_wf b.
Proof.
  sp; split; intros i.
  inversion i as [ cl w ].
  inversion w as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); simpl; intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst.
  inversion cl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  unfold isprogram, closed.
  onerw app_eq_nil_iff; repd; allrw; sp.
  allrw <- null_iff_nil.
  allrw null_remove_nvars; allsimpl.
  rw subvars_eq.
  unfold subset; sp; simpl.
  try (complete (apply_in_hyp p; sp)).
  apply isprogram_cbv; sp.
Qed.

Lemma isprog_cbv {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_cbv a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_cbv; sp.
Qed.

Lemma isprogram_halts {p} :
  forall t : @NTerm p,
    isprogram t
    -> isprogram (mk_halts t).
Proof.
  unfold mk_halts; sp.
  apply isprogram_approx.
  apply isprogram_axiom.
  apply isprogram_cbv; sp.
  allrw @nt_wf_eq; apply wf_axiom.
Qed.

Lemma isprog_halts {p} :
  forall t : @NTerm p,
    isprog t
    -> isprog (mk_halts t).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_halts; sp.
Qed.

Lemma wf_cbv {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_cbv a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_cbv_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_cbv a v b).
Proof.
  sp; split; intros i.
  apply wf_cbv; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_isect {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_isect a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_isect_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_isect a v b).
Proof.
  sp; split; intro i; try (apply wf_isect; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_isect {p} :
  forall (a : @NTerm p) v b,
    isprogram a
    -> subvars (free_vars b) [v]
    -> nt_wf b
    -> isprogram (mk_isect a v b).
Proof.
  sp.
  unfold isprogram, mk_isect, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_isect {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_isect a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_isect; sp.
Qed.

Lemma isprog_isect_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_isect a v b).
Proof.
  introv; split; intro k; try (apply isprog_isect; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_disect {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_disect a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_disect_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_disect a v b).
Proof.
  sp; split; intro i; try (apply wf_disect; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_disect {p} :
  forall (a :@NTerm p) v b,
    isprogram a
    -> subvars (free_vars b) [v]
    -> nt_wf b
    -> isprogram (mk_disect a v b).
Proof.
  sp.
  unfold isprogram, mk_disect, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_disect {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_disect a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_disect; sp.
Qed.

Lemma isprog_disect_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_disect a v b).
Proof.
  introv; split; intro k; try (apply isprog_disect; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_eisect {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_eisect a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_eisect_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_eisect a v b).
Proof.
  sp; split; intro i; try (apply wf_eisect; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_eisect {p} :
  forall (a : @NTerm p) v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_eisect a v b).
Proof.
  sp.
  unfold isprogram, mk_eisect, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_eisect {p} :
  forall (a :@NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_eisect a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_eisect; sp.
Qed.

Lemma isprog_eisect_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_eisect a v b).
Proof.
  introv; split; intro k; try (apply isprog_eisect; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_set {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_set a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_set_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_set a v b).
Proof.
  sp; split; intro i; try (apply wf_set; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_set {p} :
  forall (a : @NTerm p) v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_set a v b).
Proof.
  sp.
  unfold isprogram, mk_set, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_set {p} :
  forall (a :@NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_set a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_set; sp.
Qed.

Lemma isprog_set_iff {p} :
  forall (a :@NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_set a v b).
Proof.
  introv; split; intro k; try (apply isprog_set; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_tunion {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_tunion a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_tunion_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_tunion a v b).
Proof.
  sp; split; intro i; try (apply wf_tunion; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_tunion {p} :
  forall (a : @NTerm p) v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_tunion a v b).
Proof.
  sp.
  unfold isprogram, mk_tunion, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_tunion {p} :
  forall (a :@NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_tunion a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_tunion; sp.
Qed.

Lemma isprog_tunion_iff {p} :
  forall (a :@NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_tunion a v b).
Proof.
  introv; split; intro k; try (apply isprog_tunion; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_quotient {p} :
  forall (a : @NTerm p) v1 v2 b,
    wf_term a -> wf_term b -> wf_term (mk_quotient a v1 v2 b).
Proof.
  intros a v1 v2 B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_quotient_iff {p} :
  forall (a : @NTerm p) v1 v2 b,
    (wf_term a # wf_term b) <=> wf_term (mk_quotient a v1 v2 b).
Proof.
  sp; split; intro i; try (apply wf_quotient; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v1,v2] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_quotient {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprogram a
    -> subvars (free_vars b) [v1,v2]
    -> nt_wf b
    -> isprogram (mk_quotient a v1 v2 b).
Proof.
  sp.
  unfold isprogram, mk_quotient, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp.
  allrw subvars_prop; discover; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_quotient {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprog a
    -> isprog_vars [v1,v2] b
    -> isprog (mk_quotient a v1 v2 b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_quotient; sp.
Qed.

Lemma isprog_quotient_iff {p} :
  forall (a : @NTerm p) v1 v2 b,
    (isprog a # isprog_vars [v1,v2] b)
    <=> isprog (mk_quotient a v1 v2 b).
Proof.
  introv; split; intro k; try (apply isprog_quotient; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v1,v2] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v1 x); destruct (eq_var_dec v2 x); sp.
  right; right; right; allsimpl; sp.
Qed.

Lemma wf_w {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_w a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_w_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_w a v b).
Proof.
  sp; split; intro i; try (apply wf_w; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_w {p} :
  forall (a : @NTerm p) v b,
    isprogram a
    -> subvars (free_vars b) [v]
    -> nt_wf b
    -> isprogram (mk_w a v b).
Proof.
  sp.
  unfold isprogram, mk_w, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_w {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_w a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_w; sp.
Qed.

Lemma isprog_w_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_w a v b).
Proof.
  introv; split; intro k; try (apply isprog_w; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.


Lemma wf_m {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_m a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_m_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_m a v b).
Proof.
  sp; split; intro i; try (apply wf_m; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_m {p} :
  forall (a : @NTerm p) v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_m a v b).
Proof.
  sp.
  unfold isprogram, mk_m, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_m {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_m a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_m; sp.
Qed.


Lemma wf_pw {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    wf_term P
    -> wf_term A
    -> wf_term B
    -> wf_term C
    -> wf_term p
    -> wf_term (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  introv wP wA wB wC wp; repeat (rw <- @nt_wf_eq).
  inversion wP; inversion wA; inversion wB; inversion wC; inversion wp; constructor; sp;
  allsimpl; sp; subst; unfold num_bvars; simpl; sp;
  constructor; sp; rw @nt_wf_eq; sp.
Qed.

Lemma wf_pw_iff {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C q,
    (wf_term P
     # wf_term A
     # wf_term B
     # wf_term C
     # wf_term q)
    <=> wf_term (mk_pw P ap A bp ba B cp ca cb C q).
Proof.
  sp; split; intro i; try (apply wf_pw; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd P))
             (k (bterm [ap] A))
             (k (bterm [bp,ba] B))
             (k (bterm [cp,ca,cb] C))
             (k (nobnd q));
    intros i1 i2 i3 i4 i5.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  dest_imp i3 hyp; try (complete sp).
  dest_imp i4 hyp; try (complete sp).
  dest_imp i5 hyp; try (complete sp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst; sp.
Qed.

Lemma isprogram_pw {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprogram P
    -> subvars (free_vars A) [ap]
    -> nt_wf A
    -> subvars (free_vars B) [bp, ba]
    -> nt_wf B
    -> subvars (free_vars C) [cp, ca, cb]
    -> nt_wf C
    -> isprogram p
    -> isprogram (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  unfold isprogram, mk_pw, closed; simpl; sp.

  allrw <- null_iff_nil.
  allrw null_app.
  allrw remove_nvars_nil_l.
  allrw <- @closed_null_free_vars.
  allrw null_nil_iff.
  allunfold @isprogram; sp;
  try (complete (rw null_remove_nvars; simpl; sp;
                 allrw subvars_prop; allsimpl;
                 discover; sp)).

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_pw {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp, ba] B
    -> isprog_vars [cp, ca, cb] C
    -> isprog p
    -> isprog (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_pw; sp.
Qed.


Lemma wf_pm {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    wf_term P
    -> wf_term A
    -> wf_term B
    -> wf_term C
    -> wf_term p
    -> wf_term (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  introv wP wA wB wC wp; repeat (rw <- @nt_wf_eq).
  inversion wP; inversion wA; inversion wB; inversion wC; inversion wp; constructor; sp;
  allsimpl; sp; subst; unfold num_bvars; simpl; sp;
  constructor; sp; rw @nt_wf_eq; sp.
Qed.

Lemma wf_pm_iff {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C q,
    (wf_term P
     # wf_term A
     # wf_term B
     # wf_term C
     # wf_term q)
    <=> wf_term (mk_pm P ap A bp ba B cp ca cb C q).
Proof.
  sp; split; intro i; try (apply wf_pm; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd P))
             (k (bterm [ap] A))
             (k (bterm [bp,ba] B))
             (k (bterm [cp,ca,cb] C))
             (k (nobnd q));
    intros i1 i2 i3 i4 i5.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  dest_imp i3 hyp; try (complete sp).
  dest_imp i4 hyp; try (complete sp).
  dest_imp i5 hyp; try (complete sp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst; sp.
Qed.

Lemma isprogram_pm {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprogram P
    -> subvars (free_vars A) [ap]
    -> nt_wf A
    -> subvars (free_vars B) [bp, ba]
    -> nt_wf B
    -> subvars (free_vars C) [cp, ca, cb]
    -> nt_wf C
    -> isprogram p
    -> isprogram (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  unfold isprogram, mk_pw, closed; simpl; sp.

  allrw <- null_iff_nil.
  allrw null_app.
  allrw remove_nvars_nil_l.
  allrw <- @closed_null_free_vars.
  allrw null_nil_iff.
  allunfold @isprogram; sp;
  try (complete (rw null_remove_nvars; simpl; sp;
                 allrw subvars_prop; allsimpl;
                 discover; sp)).

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_pm {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp, ba] B
    -> isprog_vars [cp, ca, cb] C
    -> isprog p
    -> isprog (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_pm; sp.
Qed.


Lemma isprogram_function {p} :
  forall (a : @NTerm p) v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_function a v b).
Proof.
  sp.
  unfold isprogram, mk_function, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_function {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_function a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_function; sp.
Qed.

Lemma isprog_function_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_function a v b).
Proof.
  introv; split; intro k; try (apply isprog_function; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma isprogram_product {p} :
  forall (a : @NTerm p) v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_product a v b).
Proof.
  sp.
  unfold isprogram, mk_product, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- @closed_null_free_vars.
  rw null_nil_iff.
  allunfold @isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp pp; allsimpl; sp.

  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_product {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_product a v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_product; sp.
Qed.

Lemma isprog_product_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_product a v b).
Proof.
  introv; split; intro k; try (apply isprog_product; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (autodimp i1 hyp).
  repeat (autodimp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma isprogram_lam {p} :
  forall v (b : @NTerm p),
    isprog_vars [v] b
    -> isprogram (mk_lam v b).
Proof.
  sp.
  allrw @isprog_vars_eq; sp.
  constructor.
  unfold closed; simpl.
  rw app_nil_r.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
  allrw subvars_eq.
  allrw subset_singleton_r.
  apply_in_hyp pp; sp.
  constructor; allsimpl; sp; subst.
  constructor; sp.
Qed.

Lemma isprog_lam {p} :
  forall v (b : @NTerm p),
    isprog_vars [v] b
    -> isprog (mk_lam v b).
Proof.
  sp; allrw @isprog_eq; apply isprogram_lam; sp.
Qed.

Lemma isprog_vars_var {p} :
  forall v, @isprog_vars p [v] (mk_var v).
Proof.
  sp.
  rw @isprog_vars_eq; simpl; sp.
Qed.

Lemma isprog_vars_var_if {p} :
  forall v vs, LIn v vs -> @isprog_vars p vs (mk_var v).
Proof.
  sp.
  rw @isprog_vars_eq; simpl; sp.
  rw subvars_singleton_l; sp.
Qed.

Lemma isprog_vars_var_if2 {p} :
  forall v vs, LIn v vs -> @isprog_vars p vs (mk_var v) <=> True.
Proof.
  sp.
  rw @isprog_vars_eq; simpl; sp.
  rw subvars_singleton_l; sp.
Qed.

Lemma isprog_vars_var_iff {p} :
  forall v vs, LIn v vs <=> @isprog_vars p vs (mk_var v).
Proof.
  sp.
  rw @isprog_vars_eq; simpl; sp.
  rw subvars_singleton_l; sp; split; sp.
Qed.

Lemma isprog_id {p} :
  @isprog p mk_id.
Proof.
  unfold mk_id; sp; apply isprog_lam.
  apply isprog_vars_var.
Qed.
Hint Immediate isprog_id.

Lemma isprog_vsubtype {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog b
    -> isprog (mk_vsubtype a v b).
Proof.
  unfold mk_vsubtype; sp.
  apply isprog_member; sp.
  apply isprog_function; sp.
  allrw @isprog_eq.
  inversion H0.
  allunfold @closed.
  allrw @isprog_vars_eq; simpl.
  allrw; sp.
Qed.

Lemma isprog_subtype {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_subtype a b).
Proof.
  unfold mk_subtype; sp.
  apply isprog_member.
  apply isprog_lam.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp; simpl.
  apply isprog_function; sp.
  allrw @isprog_eq.
  inversion H0.
  allunfold @closed.
  rw @isprog_vars_eq; sp.
  allrw; sp.
Qed.

Lemma isprog_fun {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_fun a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_function; sp.
  allrw @isprog_vars_eq; sp; simpl.
  allrw @isprog_eq.
  inversion ipb.
  allunfold @closed.
  allrw; sp.
  allrw @isprog_eq; allunfold @isprogram; sp.
Qed.

Lemma isprog_ufun {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_ufun a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_isect; sp.
  allrw @isprog_vars_eq; sp; simpl.
  allrw @isprog_eq.
  inversion ipb.
  allunfold @closed.
  allrw; sp.
  allrw @isprog_eq; allunfold @isprogram; sp.
Qed.

Lemma isprog_eufun {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_eufun a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_eisect; sp.
  allrw @isprog_vars_eq; sp; simpl.
  allrw @isprog_eq.
  inversion ipb.
  allunfold @closed.
  allrw; sp.
  allrw @isprog_eq; allunfold @isprogram; sp.
Qed.

Lemma isprog_prod {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_prod a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_product; sp.
  allrw @isprog_vars_eq; sp; simpl.
  allrw @isprog_eq.
  inversion ipb.
  allunfold @closed.
  allrw; sp.
  allrw @isprog_eq; allunfold @isprogram; sp.
Qed.

Lemma wf_rec {p} :
  forall v (a : @NTerm p), wf_term a -> wf_term (mk_rec v a).
Proof.
  intros v a; repeat (rw <- @nt_wf_eq).
  intros nta; inversion nta; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_rec {p} :
  forall v (a : @NTerm p),
    subvars (free_vars a) [v]
    -> nt_wf a
    -> isprogram (mk_rec v a).
Proof.
  sp.
  unfold isprogram, mk_rec, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  rw null_nil_iff.
  allrw subvars_prop; allsimpl; sp.
  rw null_remove_nvars; simpl; sp.
  constructor; simpl; allunfold @isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_rec {p} :
  forall v (a : @NTerm p),
    isprog_vars [v] a
    -> isprog (mk_rec v a).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_rec; sp.
Qed.

Theorem wf_product {p} :
  forall (a : @NTerm p) v b, wf_term a -> wf_term b -> wf_term (mk_product a v b).
Proof.
  intros a v B; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_integer {p} :
  forall i, @isprogram p (mk_integer i).
Proof.
  introv.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_integer.

Lemma isprogram_int_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (Can NInt) bterms)
    -> bterms = [].
Proof.
  introv isp; inversion isp as [ cl w ].
  inversion w as [| o lnt k e]; subst; allsimpl.
  allrw <- null_iff_nil; allsimpl.
  allrw null_map.
  allrw null_iff_nil; auto.
Qed.

Lemma isprogram_nat_implies {p} :
  forall (bterms : list (@BTerm p)) n,
    isprogram (oterm (Can (Nint n)) bterms)
    -> bterms = [].
Proof.
  introv isp; inversion isp as [cl w].
  inversion w as [| o lnt k e]; subst; allsimpl.
  allrw <- null_iff_nil.
  allrw null_map.
  allrw null_iff_nil; auto.
Qed.

Lemma isprogram_integer_implies {p} :
  forall (bterms : list (@BTerm p)) z,
    isprogram (oterm (Can (Nint z)) bterms)
    -> bterms = [].
Proof.
  exact isprogram_nat_implies.
Qed.

Lemma isprogram_base_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (Can NBase) bterms)
    -> bterms = [].
Proof.
  introv isp; inversion isp as [cl w].
  inversion w as [| o lnt k e]; subst; allsimpl.
  allrw <- null_iff_nil.
  allrw null_map.
  allrw null_iff_nil; auto.
Qed.

Lemma isprogram_approx_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (Can NApprox) bterms)
    -> {a, b : NTerm $
         bterms = [nobnd a, nobnd b]}.
Proof.
  introv isp; inversion isp as [cl w].
  inversion w as [|o lnt k e]; subst; allsimpl.
  destruct bterms; allsimpl; sp.
  destruct bterms; allsimpl; sp.
  destruct bterms; allsimpl; sp.
  destruct b; destruct b0; allunfold @num_bvars; allsimpl.
  inversion e as [len].
  rewrite len in H.
  repeat (allrw length0; subst; allsimpl).
  unfold nobnd.
  exists n n0; auto.
Qed.


(* ------ programs ------ *)

Definition WTerm  {p} := { t : @NTerm p  | wf_term t }.
Definition WBTerm {p} := { bt : @BTerm p | wf_bterm bt }.

(* end hide *)

(*
  (* first of all, isprog is NOT a boolean. also, the reader will
    be left wondering what UIP_dec is*)

  where [isprog] is the Boolean version of [isprogram]
  (using a Boolean version of [isprogram] makes it easy to prove that
  closed terms are equal by proving that the underlying [NTerm]s are
  equals using [UIP_dec]).

*)

(**

  The [CTerm] type below is useful in compactly stating definitions
  that are only meaningful for closed terms. A [CTerm] is a pair
  of an [NTerm] [t] and a proof that [t] is closed.
  This [CTerm] type will be handy in compactly
  defining the Nuprl type system where types are defined as partial
  equivalence relations on closed terms.

*)

Definition CTerm {p} := { t : @NTerm p | isprog t }.
Definition get_cterm {p} (t : @CTerm p) := let (a,_) := t in a.

(* begin hide *)

Definition BCTerm {p} := { bt : @BTerm p | isprog_bt bt }.

(* end hide *)

(**

  We also define a type of terms that specifies what are the possible
  free variables of its inhabitants.  A term is a [(CVTerm vs)] term
  if the set of its free variables is a subset of [vs].  This type is
  also useful to define the Nuprl type system.  For example, to define
  a closed family of types such as a closed function type of the form
  $\NUPRLfunction{x}{A}{\NUPRLsuba{B}{z}{x}}$, $A$ has to be closed
  and the free variables of $B$ can only be $z$.

*)

Definition CVTerm {p} (vs : list NVar) := { t : @NTerm p | isprog_vars vs t }.

(* begin hide *)

Definition CVTerm3 {p} := forall a b c, @CVTerm p [a;b;c].


Definition mk_cvterm {p} (vs : list NVar) (t : @NTerm p) (p : isprog_vars vs t) :=
  exist (isprog_vars vs) t p.

Ltac destruct_cterms :=
  repeat match goal with
           | [ H : CTerm |- _ ] => destruct H
           | [ H : CVTerm _ |- _ ] => destruct H
         end.

Ltac dest_cterm H :=
  let t := type of H in
  match goal with
    | [ x : CTerm |- _ ] =>
      match t with
        | context[x] => destruct x
      end
    | [ x : CVTerm _ |- _ ] =>
      match t with
        | context[x] => destruct x
      end
  end.

(** A faster version of destruct_cterms.  We avoid destructing all of them. *)
Ltac dest_cterms H := repeat (dest_cterm H).

Definition get_wterm {p} (t : @WTerm p) := let (a,_) := t in a.
Definition get_cvterm {p} (vs : list NVar) (t : @CVTerm p vs) := let (a,_) := t in a.
Definition get_bcterm {p} (bt : @BCTerm p) := let (a,_) := bt in a.

Lemma cterm_eq {p} :
  forall t u : @CTerm p,
    get_cterm t = get_cterm u
    -> t = u.
Proof.
  introv; destruct_cterms; simpl; sp; subst.
  eauto with pi.
Qed.

Lemma cvterm_eq {p} :
  forall vs (t u : @CVTerm p vs),
    get_cvterm vs t = get_cvterm vs u
    -> t = u.
Proof.
  introv; destruct_cterms; simpl; sp; subst.
  eauto with pi.
Qed.

Lemma wf_cterm {p} :
  forall t, @wf_term p (get_cterm t).
Proof.
  introv; destruct_cterms; simpl.
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw @nt_wf_eq; sp.
Qed.
Hint Immediate wf_cterm : wf.

Lemma free_vars_cterm {p} :
  forall t : @CTerm p, free_vars (get_cterm t) = [].
Proof.
  introv; destruct_cterms; simpl.
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw; sp.
Qed.

Definition mk_cterm {p} (t : @NTerm p) (p : isprogram t) : CTerm :=
  exist isprog t (isprogram_implies t p).

Definition mk_ct {p} (t : @NTerm p) (p : isprog t) : CTerm := exist isprog t p.

Definition mk_wterm {p} (t : @NTerm p) (p : wf_term t) := exist wf_term t p.

Definition mk_wterm' {p} (t : @NTerm p) (p : nt_wf t) :=
  exist wf_term t (nt_wf_implies t p).

Definition iscvalue {p} (t : @CTerm p) : Type :=
  isvalue (get_cterm t).

Lemma mk_cv_pf {p} :
  forall vs t,
    @isprog_vars p vs (get_cterm t).
Proof.
  destruct t; simpl.
  rw @isprog_eq in i; destruct i.
  rw @isprog_vars_eq; simpl; sp.
  allunfold @closed.
  allrw; sp.
Qed.

(** From a closed term, we can always make a term whose variables
 * are contained in vs: *)
Definition mk_cv {p} (vs : list NVar) (t : @CTerm p) : CVTerm vs :=
  exist (isprog_vars vs) (get_cterm t) (mk_cv_pf vs t).

Ltac clear_deps h :=
  repeat match goal with
           | [ H : context[h] |- _ ] => clear H
         end.

Lemma programs_bt_to_program {p} :
  forall bts : list (@BCTerm p),
  forall op,
    map (fun bt => num_bvars (get_bcterm bt)) bts = OpBindings op
    -> isprogram (oterm op (map get_bcterm bts)).
Proof.
  sp; unfold isprogram; sp.
  allrw @closed_nt; sp.
  allrw in_map_iff; sp; subst.
  destruct a; destruct x; allsimpl.
  clear_deps i.
  rw <- @isprogram_bt_eq in i.
  inversion i; sp.
  constructor; sp.
  allrw in_map_iff; sp; subst.
  destruct a; destruct x; allsimpl.
  clear_deps i.
  rw <- @isprogram_bt_eq in i.
  inversion i; sp.
  rewrite <- H.
  rewrite map_map; unfold compose; sp.
Qed.

Definition mkc_int {p} : @CTerm p :=
  exist isprog mk_int isprog_int.
Definition mkw_int {p} : @WTerm p :=
  exist wf_term mk_int wf_int.

Definition mkc_integer {p} (n : Z) : @CTerm p :=
  exist isprog (mk_integer n) (isprog_mk_integer n).
Definition mkw_integer {p} (n : Z) : @WTerm p :=
  exist wf_term (mk_integer n) (wf_mk_integer n).

Lemma mkc_integer_eq {p} :
  forall a b,
    @mkc_integer p a = mkc_integer b
    -> a = b.
Proof.
  unfold mkc_integer; sp.
  inversion H; sp.
Qed.

Lemma isvalue_implies {p} :
  forall t, @isvalue p t -> (iscan t # isprogram t).
Proof.
  introv isv.
  inversion isv; subst; simpl; dands; auto.
Qed.

Lemma isvalue_iff {p} :
  forall t : @NTerm p, isvalue t <=> (iscan t # isprogram t).
Proof.
  introv; split; intro k.
  - apply isvalue_implies; auto.
  - repnd; destruct t; allsimpl; tcsp.
Qed.

Definition isprog_nout {p} (t : @NTerm p) :=
  assert (no_vars_like_b t) # wf_term t.

Definition isprog_ntseq {o} (f : @ntseq o) :=
  forall n, isprog_nout (f n).

Lemma isprog_nout_proof_irrelevance {p} :
  forall (t : @NTerm p),
  forall x y : isprog_nout t,
    x = y.
Proof.
  intros.
  destruct x, y.
  f_equal; apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : isprog_nout ?t , H2 : isprog_nout ?t |- _ ] =>
    pose proof (isprog_nout_proof_irrelevance t H2 H1) as h; subst
end : pi.

Lemma isprog_ntseq_proof_irrelevance {o} :
  forall (f : @ntseq o) (p1 p2 : isprog_ntseq f),
    p1 = p2.
Proof.
  introv.
  allunfold @isprog_ntseq.
  apply functional_extensionality_dep.
  introv.
  remember (p1 x) as i1.
  remember (p2 x) as i2.
  eauto with pi.
Qed.

Definition isprog_atom {p} : @isprog p mk_atom := (eq_refl,eq_refl).
Definition isprog_uatom {p} : @isprog p mk_uatom := (eq_refl,eq_refl).

Definition isprog_token {p} :
  forall s : String.string, @isprog p (mk_token s) := fun _ => (eq_refl,eq_refl).

Definition isprog_utoken {p} :
  forall u : get_patom_set p, @isprog p (mk_utoken u) := fun _ => (eq_refl,eq_refl).

Definition mkc_atom {p} : @CTerm p :=
  exist isprog mk_atom isprog_atom.

Definition mkc_token {p} (s : String.string) : @CTerm p :=
  exist isprog (mk_token s) (isprog_token s).

Lemma mkc_token_eq {p} :
  forall a b,
    @mkc_token p a = mkc_token b
    -> a = b.
Proof.
  introv k; inversion k; sp.
Qed.

Definition mkc_uatom {p} : @CTerm p :=
  exist isprog mk_uatom isprog_uatom.

Definition mkc_utoken {p} (u : get_patom_set p) : @CTerm p :=
  exist isprog (mk_utoken u) (isprog_utoken u).

Lemma mkc_utoken_eq {p} :
  forall a b : get_patom_set p,
    @mkc_utoken p a = mkc_utoken b
    -> a = b.
Proof.
  introv k; inversion k; sp.
Qed.

Definition mkc_nat {p} (n : nat) : @CTerm p :=
  exist isprog (mk_nat n) (isprog_mk_nat n).
Definition mkw_nat {p} (n : nat) : @WTerm p :=
  exist wf_term (mk_nat n) (wf_mk_nat n).

Definition mkc_uni {p} (i : nat) : @CTerm p :=
  exist isprog (mk_uni i) (isprog_mk_uni i).
Definition mkw_uni {p} (i : nat) : @WTerm p :=
  exist wf_term (mk_uni i) (wf_mk_uni i).

Lemma mkc_uni_eq {p} :
  forall a b,
    @mkc_uni p a = mkc_uni b
    -> a = b.
Proof.
  unfold mkc_uni; sp.
  inversion H; sp.
Qed.

Definition mkc_base {p} : @CTerm p :=
  exist isprog mk_base isprog_base.
Definition mkw_base {p} : @WTerm p :=
  exist wf_term mk_base wf_base.

Definition mkc_axiom {p} : @CTerm p :=
  exist isprog mk_axiom isprog_axiom.
Definition mkw_axiom {p} : @WTerm p :=
  exist wf_term mk_axiom wf_axiom.

Definition mkc_bottom {p} : @CTerm p :=
  exist isprog mk_bottom isprog_bottom.

Lemma isprogram_pair {p} :
  forall (a b : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram (mk_pair a b).
Proof.
  introv pa pb.
  inversion pa; inversion pb.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold @closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_pair {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_pair a b).
Proof.
  sp; allrw @isprog_eq; apply isprogram_pair; sp.
Qed.

Definition mkc_pair {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_pair a b) (isprog_pair a b x y).


Theorem wf_sup {p} :
  forall a b : @NTerm p, wf_term a -> wf_term b -> wf_term (mk_sup a b).
Proof.
  intros a b; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_sup {p} :
  forall a b : @NTerm p,
    isprogram a
    -> isprogram b
    -> isprogram (mk_sup a b).
Proof.
  introv pa pb.
  inversion pa; inversion pb.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold @closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprogram_sup_iff {p} :
  forall a b : @NTerm p, (isprogram a # isprogram b) <=> isprogram (mk_sup a b).
Proof.
  intros; split; intro i.
  apply isprogram_sup; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_sup {p} :
  forall a b : @NTerm p, isprog a -> isprog b -> isprog (mk_sup a b).
Proof.
  sp; allrw @isprog_eq; apply isprogram_sup; sp.
Qed.

Definition mkc_sup {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_sup a b) (isprog_sup a b x y).

Lemma mkc_sup_eq {p} :
  forall a b c d : @CTerm p,
    mkc_sup a b = mkc_sup c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold @mkc_sup.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_pair_eq {p} :
  forall a b c d : @CTerm p,
    mkc_pair a b = mkc_pair c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold @mkc_pair.
  inversion H; subst.
  eauto with pi.
Qed.

Theorem wf_refl {p} :
  forall a : @NTerm p, wf_term a -> wf_term (mk_refl a).
Proof.
  intros a; repeat (rw <- @nt_wf_eq).
  intros nta; inversion nta; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_refl {p} :
  forall a : @NTerm p,
    isprogram a
    -> isprogram (mk_refl a).
Proof.
  introv pa.
  inversion pa.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold @closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprogram_refl_iff {p} :
  forall a : @NTerm p, isprogram a <=> isprogram (mk_refl a).
Proof.
  intros; split; intro i.
  apply isprogram_refl; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_refl {p} :
  forall a : @NTerm p, isprog a -> isprog (mk_refl a).
Proof.
  sp; allrw @isprog_eq; apply isprogram_refl; sp.
Qed.

Definition mkc_refl {p} (t1 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
    exist isprog (mk_refl a) (isprog_refl a x).

Lemma mkc_refl_eq {p} :
  forall a b : @CTerm p,
    mkc_refl a = mkc_refl b
    -> a = b.
Proof.
  intros.
  destruct a, b.
  allunfold @mkc_refl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_texc {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_texc a b) (isprog_texc a b x y).

Lemma mkc_texc_eq {p} :
  forall A1 A2 B1 B2 : @CTerm p,
    mkc_texc A1 A2 = mkc_texc B1 B2
    -> A1 = B1 # A2 = B2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  dands; eauto with pi.
Qed.

Definition mkc_union {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_union a b) (isprog_union a b x y).

Lemma mkc_union_eq {p} :
  forall A1 A2 B1 B2 : @CTerm p,
    mkc_union A1 A2 = mkc_union B1 B2
    -> A1 = B1 # A2 = B2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_eunion {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_eunion a b) (isprog_eunion a b x y).

Lemma mkc_eunion_eq {p} :
  forall A1 A2 B1 B2 : @CTerm p,
    mkc_eunion A1 A2 = mkc_eunion B1 B2
    -> A1 = B1 # A2 = B2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_union2 {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_union2 a b) (isprog_union2 a b x y).

Lemma mkc_union2_eq {p} :
  forall A1 A2 B1 B2 : @CTerm p,
    mkc_union2 A1 A2 = mkc_union2 B1 B2
    -> A1 = B1 # A2 = B2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma isprog_unit {p} : @isprog p mk_unit.
Proof.
  unfold isprog; simpl.
  rw assert_true_iff; dands; sp.
Qed.
Hint Immediate isprog_unit.

Definition mkc_bool {p} : @CTerm p :=
  exist isprog mk_bool (isprog_union mk_unit mk_unit isprog_unit isprog_unit).

Lemma isprogram_inl {p} :
  forall a : @NTerm p, isprogram a -> isprogram (mk_inl a).
Proof.
  introv pa.
  inversion pa.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold @closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_inl {p} :
  forall a : @NTerm p, isprog a -> isprog (mk_inl a).
Proof.
  sp; allrw @isprog_eq; apply isprogram_inl; sp.
Qed.

Definition mkc_inl {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in exist isprog (mk_inl a) (isprog_inl a x).

Lemma isprogram_inr {p} :
  forall a : @NTerm p, isprogram a -> isprogram (mk_inr a).
Proof.
  introv pa.
  inversion pa.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold @closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_inr {p} :
  forall a : @NTerm p, isprog a -> isprog (mk_inr a).
Proof.
  sp; allrw @isprog_eq; apply isprogram_inr; sp.
Qed.

Definition mkc_inr {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in exist isprog (mk_inr a) (isprog_inr a x).

Lemma mkc_inl_eq {p} :
  forall a b : @CTerm p,
    mkc_inl a = mkc_inl b
    -> a = b.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_inr_eq {p} :
  forall a b : @CTerm p,
    mkc_inr a = mkc_inr b
    -> a = b.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_pertype {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_pertype a) (isprog_pertype a x).
Definition mkw_pertype {p} (R : @WTerm p) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_pertype a) (wf_pertype a x).

Lemma mkc_pertype_eq {p} :
  forall R1 R2 : @CTerm p, mkc_pertype R1 = mkc_pertype R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_partial {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_partial a) (isprog_partial a x).
Definition mkw_partial {p} (R : @WTerm p) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_partial a) (wf_partial a x).

Lemma mkc_partial_eq {p} :
  forall R1 R2 : @CTerm p, mkc_partial R1 = mkc_partial R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_ipertype {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_ipertype a) (isprog_ipertype a x).
Definition mkw_ipertype {p} (R : @WTerm p) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_ipertype a) (wf_ipertype a x).

Lemma mkc_ipertype_eq {p} :
  forall R1 R2 : @CTerm p, mkc_ipertype R1 = mkc_ipertype R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_spertype {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_spertype a) (isprog_spertype a x).
Definition mkw_spertype {p} (R : @WTerm p) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_spertype a) (wf_spertype a x).

Lemma mkc_spertype_eq {p} :
  forall R1 R2 : @CTerm p, mkc_spertype R1 = mkc_spertype R2 -> R1 = R2.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto with pi.
Qed.

Definition mkc_tuni {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_tuni a) (isprog_tuni a x).

Lemma mkc_tuni_eq {p} :
  forall R1 R2 : @CTerm p, mkc_tuni R1 = mkc_tuni R2 -> R1 = R2.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto with pi.
Qed.

Lemma wf_sleep {p} :
  forall a : @NTerm p, wf_term a -> wf_term (mk_sleep a).
Proof.
  introv h.
  apply nt_wf_eq; apply nt_wf_eq in h.
  intros; inversion h; subst;
  constructor; allsimpl; sp;
  subst; auto; simpl; constructor; auto.
Qed.

Lemma isprogram_sleep {p} :
  forall a : @NTerm p, isprogram a -> isprogram (mk_sleep a).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_sleep; sp.
Qed.

Lemma isprogram_sleep_iff {p} :
  forall a : @NTerm p, isprogram a <=> isprogram (mk_sleep a).
Proof.
  intros; split; intro i.
  apply isprogram_sleep; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_sleep {p} :
  forall a : @NTerm p, isprog a -> isprog (mk_sleep a).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_sleep; auto.
Qed.

Definition mkc_sleep {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_sleep a) (isprog_sleep a x).

Lemma mkc_sleep_eq {p} :
  forall a b : @CTerm p, mkc_sleep a = mkc_sleep b -> a = b.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto with pi.
Qed.

Lemma wf_exception {p} :
  forall a (e : @NTerm p),
    wf_term a
    -> wf_term e
    -> wf_term (mk_exception a e).
Proof.
  introv h1 h2.
  allrw <- @nt_wf_eq.
  intros; inversion h1; inversion h2; subst;
  constructor; allsimpl; sp;
  subst; auto; simpl; constructor; auto.
Qed.

Lemma isprogram_exception {p} :
  forall a (e : @NTerm p),
    isprogram a
    -> isprogram e
    -> isprogram (mk_exception a e).
Proof.
  sp; allunfold @isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw @nt_wf_eq.
  apply wf_exception; sp.
Qed.

Lemma isprogram_exception_iff {p} :
  forall a (e : @NTerm p),
    isprogram (mk_exception a e) <=> (isprogram a # isprogram e).
Proof.
  intros; split; intro i.
  - inversion i as [cl w].
    allunfold @closed; allsimpl.
    allrw remove_nvars_nil_l.
    allrw app_nil_r.
    allrw app_eq_nil_iff; repnd; allrw.
    inversion w as [| o lnt k meq ]; allsimpl; subst.
    generalize (k (nobnd a)) (k (nobnd e)); intros i1 i2.
    dest_imp i1 hyp.
    dest_imp i2 hyp.
    unfold isprogram; allrw.
    inversion i1; subst; sp.
    inversion i2; subst; sp.
  - apply isprogram_exception; sp.
Qed.

Lemma isprog_exception {p} :
  forall a (e : @NTerm p),
    isprog a
    -> isprog e
    -> isprog (mk_exception a e).
Proof.
  sp.
  allrw @isprog_eq.
  apply isprogram_exception; auto.
Qed.

Definition mkc_exception {p} (a e : @CTerm p) : CTerm :=
  let (u,y) := a in
  let (t,x) := e in
    exist isprog (mk_exception u t) (isprog_exception u t y x).

Lemma mkc_exception_eq {p} :
  forall a b (t u : @CTerm p),
    mkc_exception a t = mkc_exception b u
    -> (a = b # t = u).
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  dands; eauto with pi.
Qed.

Lemma wf_try {p} :
  forall (a : @NTerm p) x v b,
    wf_term a
    -> wf_term x
    -> wf_term b
    -> wf_term (mk_try a x v b).
Proof.
  introv; repeat (rw <- @nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_try_iff {p} :
  forall (a : @NTerm p) x v b,
    (wf_term a # wf_term x # wf_term b) <=> wf_term (mk_try a x v b).
Proof.
  sp; split; intros i.
  apply wf_try; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst.
  generalize (k (nobnd a)) (k (nobnd x)) (k (bterm [v] b)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprogram_try {p} :
  forall (a : @NTerm p) x v b,
    isprogram a
    -> isprogram x
    -> subvars (free_vars b) [v]
    -> nt_wf b
    -> isprogram (mk_try a x v b).
Proof.
  sp.
  repeat constructor; sp.
  - unfold closed; simpl.
    allrw remove_nvars_nil_l.
    allrw app_nil_r.
    allrw app_eq_nil_iff; sp.
    + allunfold @isprogram; allunfold @closed; sp.
    + allunfold @isprogram; allunfold @closed; sp.
    + allrw subvars_eq.
      rw <- null_iff_nil.
      rw null_remove_nvars; simpl; sp.
  - allsimpl; sp; subst.
    + constructor; allunfold @isprogram; sp.
    + constructor; allunfold @isprogram; sp.
    + constructor; sp.
Qed.

Lemma isprogram_try_iff {p} :
  forall (a : @NTerm p) x v b,
    isprogram (mk_try a x v b)
    <=> isprogram a
        # isprogram x
        # subvars (free_vars b) [v]
        # nt_wf b.
Proof.
  sp; split; intros i.
  - inversion i as [ cl w ].
    inversion w as [| o lnt k e ]; subst; allsimpl.
    generalize (k (nobnd a)) (k (nobnd x)) (k (bterm [v] b)); simpl; intros i1 i2 i3.
    dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
    inversion i1; inversion i2; inversion i3; subst.
    inversion cl.
    allrw remove_nvars_nil_l.
    allrw app_nil_r.
    unfold isprogram, closed.
    onerw app_eq_nil_iff; repd; allrw; sp;
    onerw app_eq_nil_iff; repd; allrw; sp.
    allrw <- null_iff_nil.
    allrw null_remove_nvars; allsimpl.
    rw subvars_eq.
    unfold subset; sp; simpl.
  - apply isprogram_try; sp.
Qed.

Lemma isprogram_try_iff2 {p} :
  forall (a : @NTerm p) x v b,
    isprogram (mk_try a x v b)
    <=> isprogram a # isprogram x # isprogram_bt (bterm [v] b).
Proof.
  introv.
  rw @isprogram_try_iff.
  unfold isprogram_bt; simpl.
  unfold closed_bt; simpl.
  rw <- null_iff_nil.
  rw null_remove_nvars.
  rw subvars_prop.
  split; intro k; repnd; dands; auto.
  inversion k; sp.
Qed.

Lemma isprog_try {p} :
  forall (a : @NTerm p) x v b,
    isprog a
    -> isprog x
    -> isprog_vars [v] b
    -> isprog (mk_try a x v b).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.
  apply isprogram_try; sp.
Qed.

Definition mkc_try {p} (t1 : @CTerm p) (n : @CTerm p) (v : NVar) (t2 : CVTerm [v]) : CTerm :=
  let (a,x) := t1 in
  let (c,z) := n in
  let (b,y) := t2 in
    exist isprog (mk_try a c v b) (isprog_try a c v b x z y).

(*
Definition mkc_esquash (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_esquash a) (isprog_esquash a x).
Definition mkw_esquash (R : WTerm) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_esquash a) (wf_esquash a x).

Lemma mkc_esquash_eq :
  forall R1 R2, mkc_esquash R1 = mkc_esquash R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
*)

Definition mkc_isinl {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_isinl a b c) (isprog_isinl a b c x y z).

Lemma mkc_isinl_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_isinl a b c = mkc_isinl d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Definition mkc_isinr {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_isinr a b c) (isprog_isinr a b c x y z).

Lemma mkc_isinr_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_isinr a b c = mkc_isinr d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Definition mkc_ispair {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_ispair a b c) (isprog_ispair a b c x y z).

Lemma mkc_ispair_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_ispair a b c = mkc_ispair d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Definition mkc_isaxiom {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_isaxiom a b c) (isprog_isaxiom a b c x y z).

Lemma mkc_isaxiom_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_isinl a b c = mkc_isaxiom d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
Qed.


Definition mkc_islambda {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_islambda a b c) (isprog_islambda a b c x y z).

Lemma mkc_islambda_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_isinl a b c = mkc_islambda d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
Qed.


Definition mkc_can_test {p} (test: CanonicalTest) (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_can_test test a b c) (isprog_can_test test a b c x y z).


Definition mk_approx_c {p} (t1 t2 : @CTerm p) : NTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    mk_approx a b.
Definition mkc_approx {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_approx a b) (isprog_approx a b x y).
Definition mkw_approx {p} (t1 t2 : @WTerm p) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_approx a b) (wf_approx a b x y).
Lemma mkw_approx_eq {p} :
  forall a b c d : @WTerm p,
    mkw_approx a b = mkw_approx c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold @mkw_approx.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_approx_eq {p} :
  forall a b c d : @CTerm p,
    mkc_approx a b = mkc_approx c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold @mkc_approx.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_cequiv {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_cequiv a b) (isprog_cequiv a b x y).
Definition mkw_cequiv {p} (t1 t2 : @WTerm p) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_cequiv a b) (wf_cequiv a b x y).
Lemma mkw_cequiv_eq {p} :
  forall a b c d : @WTerm p,
    mkw_cequiv a b = mkw_cequiv c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold @mkw_cequiv.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_cequiv_eq {p} :
  forall a b c d : @CTerm p,
    mkc_cequiv a b = mkc_cequiv c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold @mkc_cequiv.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_compute {p} (t1 t2 n : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := n in
    exist isprog (mk_compute a b c) (isprog_compute a b c x y z).
Lemma mkc_compute_eq {p} :
  forall a b c d n m : @CTerm p,
    mkc_compute a b n = mkc_compute c d m
    -> a = c # b = d # n = m.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Definition mkc_image {p} (T F : @CTerm p) : CTerm :=
  let (t,x) := T in
  let (f,y) := F in
    exist isprog (mk_image t f) (isprog_image t f x y).

Lemma mkc_image_eq {p} :
  forall A1 A2 f1 f2 : @CTerm p,
    mkc_image A1 f1 = mkc_image A2 f2
    -> A1 = A2 # f1 = f2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

(* end hide *)

(**

  Using the [CVTerm] and [CTerm] types we can define useful
  abstraction to build closed versions of the various terms of our
  computation system.  For example, given a variable [v] and a term in
  [CVTerm [v]], we can build a closed lambda abstraction.  As an other
  example, given two closed terms, we can build a closed application
  term.

 *)

Definition mkc_lam {p} (v : NVar) (b : @CVTerm p [v]) : CTerm :=
  let (t,x) := b in
  exist isprog (mk_lam v t) (isprog_lam v t x).

Definition mkc_apply {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_apply a b) (isprog_apply a b x y).

(* begin hide *)

Lemma mkc_apply_eq {p} :
  forall t1 t2 t3 t4 : @CTerm p,
    mkc_apply t1 t2 = mkc_apply t3 t4 -> t1 = t3 # t2 = t4.
Proof.
  introv e; destruct_cterms; allsimpl.
  inversion e; subst.
  irr; sp.
Qed.

Definition mkw_apply {p} (t1 t2 : @WTerm p) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_apply a b) (wf_apply a b x y).

Definition mkc_apply2 {p} (t0 t1 t2 : @CTerm p) : CTerm :=
  let (f,z) := t0 in
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_apply2 f a b) (isprog_apply2 f a b z x y).

Lemma mkc_apply2_eq {p} :
  forall t0 t1 t2 : @CTerm p,
    mkc_apply2 t0 t1 t2 = mkc_apply (mkc_apply t0 t1) t2.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Theorem wf_apply3 {p} :
  forall f a b c : @NTerm p,
    wf_term f
    -> wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term (mk_apply3 f a b c).
Proof.
  unfold mk_apply3; sp.
  repeat (apply wf_apply); auto.
Qed.

Theorem isprogram_apply3 {p} :
  forall f a b c : @NTerm p,
    isprogram f
    -> isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_apply3 f a b c).
Proof.
  unfold mk_apply3; sp.
  repeat (apply isprogram_apply); auto.
Qed.

Theorem isprog_apply3 {p} :
  forall f a b c : @NTerm p,
    isprog f
    -> isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_apply3 f a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_apply3; auto.
Qed.

Definition mkc_apply3 {p} (t0 t1 t2 t3 : @CTerm p) : CTerm :=
  let (f,u) := t0 in
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_apply3 f a b c) (isprog_apply3 f a b c u x y z).

Lemma mkc_apply3_eq {p} :
  forall t0 t1 t2 t3 : @CTerm p,
    mkc_apply3 t0 t1 t2 t3 = mkc_apply (mkc_apply (mkc_apply t0 t1) t2) t3.
Proof.
  intros; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_eapply {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_eapply a b) (isprog_eapply a b x y).

Lemma mkc_eapply_eq {p} :
  forall t1 t2 t3 t4 : @CTerm p,
    mkc_eapply t1 t2 = mkc_eapply t3 t4 -> t1 = t3 # t2 = t4.
Proof.
  introv e; destruct_cterms; allsimpl.
  inversion e; subst.
  irr; sp.
Qed.

(*
Definition mkc_apseq {p} f (t : @CTerm p) : CTerm :=
  let (a,x) := t in
    exist isprog (mk_apseq f a) (isprog_apseq f a x).

Lemma mkc_apseq_eq {p} :
  forall f1 f2 (t1 t2 : @CTerm p),
    mkc_apseq f1 t1 = mkc_apseq f2 t2 -> f1 = f2 # t1 = t2.
Proof.
  introv e; destruct_cterms; allsimpl.
  inversion e; subst.
  irr; sp.
Qed.
 *)

(*Definition mkw_apply2 (t0 t1 t2 : WTerm) : WTerm :=
  let (f,z) := t0 in
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_apply2 f a b) (wf_apply2 f a b z x y).*)

Definition mkc_free_from_atom {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_free_from_atom a b c) (isprog_free_from_atom a b c x y z).

Lemma mkc_free_from_atom_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_free_from_atom a b c = mkc_free_from_atom d e f
    -> a = d # b = e # c = f.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto 6 with pi.
Qed.

Definition mkc_efree_from_atom {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_efree_from_atom a b c) (isprog_efree_from_atom a b c x y z).

Lemma mkc_efree_from_atom_eq {p} :
  forall a b c d e f : @CTerm p,
    mkc_efree_from_atom a b c = mkc_efree_from_atom d e f
    -> a = d # b = e # c = f.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto 6 with pi.
Qed.

Definition mkc_free_from_atoms {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_free_from_atoms a b) (isprog_free_from_atoms a b x y).

Lemma mkc_free_from_atoms_eq {p} :
  forall a b c d : @CTerm p,
    mkc_free_from_atoms a b = mkc_free_from_atoms c d
    -> a = c # b = d.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto 6 with pi.
Qed.

Definition mkc_free_from_defs {p} (T t : @CTerm p) : CTerm :=
  let (a,x) := T in
  let (b,y) := t in
  exist isprog (mk_free_from_defs a b) (isprog_free_from_defs a b x y).

Lemma mkc_free_from_defs_eq {p} :
  forall (a b c d : @CTerm p),
    mkc_free_from_defs a b = mkc_free_from_defs c d
    -> a = c # b = d.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto 6 with pi.
Qed.

Definition mkc_equality {p} (t1 t2 T : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist isprog (mk_equality a b c) (isprog_equality a b c x y z).
Definition mkw_equality {p} (t1 t2 T : @WTerm p) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist wf_term (mk_equality a b c) (wf_equality a b c x y z).
Lemma mkw_equality_eq {p} :
  forall a b c d T U : @WTerm p,
    mkw_equality a b T = mkw_equality c d U
    -> a = c # b = d # T = U.
Proof.
  intros.
  destruct a, b, c, d, T, U.
  allunfold @mkw_equality.
  inversion H; subst.
  eauto 6 with pi.
Qed.
Lemma mkc_equality_eq {p} :
  forall a b c d T U : @CTerm p,
    mkc_equality a b T = mkc_equality c d U
    -> a = c # b = d # T = U.
Proof.
  intros.
  destruct a, b, c, d, T, U.
  allunfold @mkc_equality.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Definition mkc_member {p} (t T : @CTerm p) : CTerm :=
  let (a,x) := t in
  let (b,y) := T in
    exist isprog (mk_member a b) (isprog_member a b x y).

Lemma fold_mkc_member {p} :
  forall t T : @CTerm p,
    mkc_equality t t T = mkc_member t T.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_requality {p} (t1 t2 T : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist isprog (mk_requality a b c) (isprog_requality a b c x y z).

Definition mkw_requality {p} (t1 t2 T : @WTerm p) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist wf_term (mk_requality a b c) (wf_requality a b c x y z).

Lemma mkw_requality_eq {p} :
  forall a b c d T U : @WTerm p,
    mkw_requality a b T = mkw_requality c d U
    -> a = c # b = d # T = U.
Proof.
  intros.
  destruct a, b, c, d, T, U.
  allunfold @mkw_requality.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Lemma mkc_requality_eq {p} :
  forall a b c d T U : @CTerm p,
    mkc_requality a b T = mkc_requality c d U
    -> a = c # b = d # T = U.
Proof.
  intros.
  destruct a, b, c, d, T, U.
  allunfold @mkc_requality.
  inversion H; subst.
  eauto 6 with pi.
Qed.

Definition mkc_rmember {p} (t T : @CTerm p) : CTerm :=
  let (a,x) := t in
  let (b,y) := T in
    exist isprog (mk_rmember a b) (isprog_rmember a b x y).

Lemma fold_mkc_rmember {p} :
  forall t T : @CTerm p,
    mkc_requality t t T = mkc_rmember t T.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_tequality {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_tequality a b) (isprog_tequality a b x y).

Lemma mkc_tequality_eq {p} :
  forall a b c d : @CTerm p,
    mkc_tequality a b = mkc_tequality c d
    -> a = c # b = d.
Proof.
  intros.
  destruct_cterms.
  allunfold @mkc_tequality.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_type {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in exist isprog (mk_type a) (isprog_type a x).

Lemma fold_mkc_type {p} :
  forall t : @CTerm p, mkc_tequality t t = mkc_type t.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_cbv {p} (t1 : @CTerm p) (v : NVar) (t2 : CVTerm [v]) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_cbv a v b) (isprog_cbv a v b x y).

Definition mkc_halts {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in
    exist isprog (mk_halts a) (isprog_halts a x).

Lemma isprog_vars_axiom {p} :
  forall v,
    @isprog_vars p [v] mk_axiom.
Proof.
  unfold isprog_vars; sp.
Qed.

Definition mkcv_axiom {p} (v : NVar) : @CVTerm p [v] :=
  exist (isprog_vars [v]) mk_axiom (isprog_vars_axiom v).

Lemma fold_mkc_halts {p} :
  forall t : @CTerm p,
    mkc_approx mkc_axiom (mkc_cbv t nvarx (mkcv_axiom nvarx)) = mkc_halts t.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Lemma isprogram_spread {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprogram a
    -> subvars (free_vars b) [v1,v2]
    -> nt_wf b
    -> isprogram (mk_spread a v1 v2 b).
Proof.
  unfold isprogram, closed; introv ipa sv ntb; repnd; simpl.
  allrw; simpl.
  allrw subvars_prop; allsimpl.
  allrw app_nil_r.
  rw <- null_iff_nil; rw null_remove_nvars.
  dands.

  introv i.
  apply sv in i; sp.

  constructor; simpl.

  introv e; repdors; subst; try (complete sp).
  constructor; sp.

  constructor.
Qed.

Lemma isprog_spread {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprog a
    -> isprog_vars [v1,v2] b
    -> isprog (mk_spread a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw @isprog_eq.
  allrw @isprog_vars_eq.
  apply isprogram_spread; sp.
Qed.

Definition mkc_spread {p}
           (t1 : @CTerm p)
           (v1 v2 : NVar)
           (t2 : CVTerm [v1,v2]) : CTerm :=
  let (a,x1) := t1 in
  let (b,x2) := t2 in
    exist isprog (mk_spread a v1 v2 b) (isprog_spread a v1 v2 b x1 x2).

Lemma mkc_spread_eq1 {p} :
  forall (a1 : @CTerm p) x1 y1 b1 a2 x2 y2 b2,
    mkc_spread a1 x1 y1 b1 = mkc_spread a2 x2 y2 b2
    -> a1 = a2 # x1 = x2 # y1 = y2.
Proof.
  introv e.
  destruct a1, a2, b1, b2.
  allunfold @mkc_spread.
  inversion e; subst.
  eauto with pi.
Qed.
Lemma mkc_spread_eq2 {p} :
  forall (a : @CTerm p) x y b1 b2,
    mkc_spread a x y b1 = mkc_spread a x y b2
    -> b1 = b2.
Proof.
  introv e.
  destruct a, b1, b2.
  allunfold @mkc_spread.
  inversion e; subst.
  eauto with pi.
Qed.

Lemma isprogram_dsup {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprogram a
    -> subvars (free_vars b) [v1,v2]
    -> nt_wf b
    -> isprogram (mk_dsup a v1 v2 b).
Proof.
  unfold isprogram, closed; introv ipa sv ntb; repnd; simpl.
  allrw; simpl.
  allrw subvars_prop; allsimpl.
  allrw app_nil_r.
  rw <- null_iff_nil; rw null_remove_nvars.
  dands.

  introv i.
  apply sv in i; sp.

  constructor; simpl.

  introv e; repdors; subst; try (complete sp).
  constructor; sp.

  constructor.
Qed.

Lemma isprog_dsup {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprog a
    -> isprog_vars [v1,v2] b
    -> isprog (mk_dsup a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw @isprog_eq.
  allrw @isprog_vars_eq.
  apply isprogram_dsup; sp.
Qed.

Definition mkc_dsup {p}
           (t1 : @CTerm p)
           (v1 v2 : NVar)
           (t2 : CVTerm [v1,v2]) : CTerm :=
  let (a,x1) := t1 in
  let (b,x2) := t2 in
    exist isprog (mk_dsup a v1 v2 b) (isprog_dsup a v1 v2 b x1 x2).



Lemma isprogram_decide {p} :
  forall (a : @NTerm p) v1 a1 v2 a2,
    isprogram a
    -> subvars (free_vars a1) [v1]
    -> nt_wf a1
    -> subvars (free_vars a2) [v2]
    -> nt_wf a2
    -> isprogram (mk_decide a v1 a1 v2 a2).
Proof.
  unfold isprogram, closed; introv ipa sv1 nt1 sv2 nt2; repnd; simpl.
  allrw; simpl.
  allrw subvars_eq.
  unfold subset in sv1, sv2; sp.
  assert (remove_nvars [v1] (free_vars a1) = []) as eq1.
  rw <- null_iff_nil; rw null_remove_nvars; introv ia1.
  apply sv1 in ia1; sp.
  assert (remove_nvars [v2] (free_vars a2) = []) as eq2.
  rw <- null_iff_nil; rw null_remove_nvars; introv ia2.
  apply sv2 in ia2; sp.
  rw eq1; rw eq2; sp.
  repeat (constructor; simpl; sp; subst).
Qed.

Lemma isprog_decide {p} :
  forall (a : @NTerm p) v1 a1 v2 a2,
    isprog a
    -> isprog_vars [v1] a1
    -> isprog_vars [v2] a2
    -> isprog (mk_decide a v1 a1 v2 a2).
Proof.
  introv ipa ipa1 ipa2.
  allrw @isprog_eq.
  allrw @isprog_vars_eq.
  apply isprogram_decide; sp.
Qed.

Definition mkc_decide {p}
           (t : @CTerm p)
           (v1 : NVar)
           (t1 : CVTerm [v1])
           (v2 : NVar)
           (t2 : CVTerm [v2]) : CTerm :=
  let (a,x) := t in
  let (a1,x1) := t1 in
  let (a2,x2) := t2 in
    exist isprog (mk_decide a v1 a1 v2 a2) (isprog_decide a v1 a1 v2 a2 x x1 x2).

Definition mkc_ite {p} (a b c : @CTerm p) :=
  let (t1,x1) := a in
  let (t2,x2) := b in
  let (t3,x3) := c in
  exist isprog
        (mk_decide t1 nvarx t2 nvarx t3)
        (isprog_decide t1 nvarx t2 nvarx t3
                       x1
                       (isprog_vars_if_isprog [nvarx] t2 x2)
                       (isprog_vars_if_isprog [nvarx] t3 x3)).

Lemma mkc_ite_eq_mkc_decide {p} :
  forall a b c : @CTerm p,
    mkc_ite a b c = mkc_decide a nvarx (mk_cv [nvarx] b) nvarx (mk_cv [nvarx] c).
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_isect {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_isect a v b) (isprog_isect a v b x y).
Definition mkw_isect {p} (T1 : @WTerm p) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_isect a v b) (wf_isect a v b x y).
Lemma mkw_isect_eq {p} :
  forall (a1 : @WTerm p) v1 b1 a2 v2 b2,
    mkw_isect a1 v1 b1 = mkw_isect a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkw_isect.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_isect_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_isect a1 v1 b1 = mkc_isect a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_isect.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_isect_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_isect a v b1 = mkc_isect a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_isect.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_uall {p} := @mkc_isect p.

Definition mkc_eisect {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_eisect a v b) (isprog_eisect a v b x y).

Lemma mkc_eisect_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_eisect a1 v1 b1 = mkc_eisect a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_eisect.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_eisect_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_eisect a v b1 = mkc_eisect a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_eisect.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_disect {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_disect a v b) (isprog_disect a v b x y).
Definition mkw_disect {p} (T1 : @WTerm p) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_disect a v b) (wf_disect a v b x y).
Lemma mkw_disect_eq {p} :
  forall (a1 : @WTerm p) v1 b1 a2 v2 b2,
    mkw_disect a1 v1 b1 = mkw_disect a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkw_disect.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_disect_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_disect a1 v1 b1 = mkc_disect a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_disect.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_disect_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_disect a v b1 = mkc_disect a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_disect.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_set {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_set a v b) (isprog_set a v b x y).

Lemma mkc_set_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_set a1 v1 b1 = mkc_set a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_set.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_set_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_set a v b1 = mkc_set a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_set.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_tunion {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_tunion a v b) (isprog_tunion a v b x y).

Lemma mkc_tunion_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_tunion a1 v1 b1 = mkc_tunion a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_tunion.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_tunion_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_tunion a v b1 = mkc_tunion a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_tunion.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_quotient {p} (T1 : @CTerm p) (v1 v2 : NVar) (T2 : CVTerm [v1,v2]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_quotient a v1 v2 b) (isprog_quotient a v1 v2 b x y).

Lemma mkc_quotient_eq1 {p} :
  forall (a1 : @CTerm p) v1 u1 b1 a2 v2 u2 b2,
    mkc_quotient a1 v1 u1 b1 = mkc_quotient a2 v2 u2 b2
    -> a1 = a2 # v1 = v2 # u1 = u2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_quotient.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_quotient_eq2 {p} :
  forall (a : @CTerm p) v1 v2 b1 b2,
    mkc_quotient a v1 v2 b1 = mkc_quotient a v1 v2 b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_quotient.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_w {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_w a v b) (isprog_w a v b x y).
Definition mkw_w {p} (T1 : @WTerm p) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_w a v b) (wf_w a v b x y).
Lemma mkw_w_eq {p} :
  forall (a1 : @WTerm p) v1 b1 a2 v2 b2,
    mkw_w a1 v1 b1 = mkw_w a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkw_w.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_w_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_w a1 v1 b1 = mkc_w a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_w.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_w_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_w a v b1 = mkc_w a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_w.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_m {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_m a v b) (isprog_m a v b x y).
Definition mkw_m {p} (T1 : @WTerm p) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_m a v b) (wf_w a v b x y).
Lemma mkw_m_eq {p} :
  forall (a1 : @WTerm p) v1 b1 a2 v2 b2,
    mkw_m a1 v1 b1 = mkw_m a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkw_m.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_m_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_m a1 v1 b1 = mkc_m a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_w.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_m_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_m a v b1 = mkc_m a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_w.
  inversion H; subst.
  eauto with pi.
Qed.



Definition mkc_pw {p}
           (P : @CTerm p)
           (ap : NVar) (A : CVTerm [ap])
           (bp : NVar) (ba : NVar) (B : CVTerm [bp, ba])
           (cp : NVar) (ca : NVar) (cb : NVar) (C : CVTerm [cp, ca, cb])
           (p : CTerm) : CTerm :=
  let (tP,wP) := P in
  let (tA,wA) := A in
  let (tB,wB) := B in
  let (tC,wC) := C in
  let (tp,wp) := p in
    exist isprog
          (mk_pw tP ap tA bp ba tB cp ca cb tC tp)
          (isprog_pw tP ap tA bp ba tB cp ca cb tC tp wP wA wB wC wp).


Lemma mkc_pw_eq1 {p} :
  forall (P1 : @CTerm p) ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2,
    mkc_pw P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
    = mkc_pw P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
    -> P1 = P2
       # p1 = p2
       # ap1 = ap2
       # bp1 = bp2
       # ba1 = ba2
       # cp1 = cp2
       # ca1 = ca2
       # cb1 = cb2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

Lemma mkc_pw_eq2 {p} :
  forall (P : @CTerm p) ap bp ba cp ca cb p A1 B1 C1 A2 B2 C2,
    mkc_pw P ap A1 bp ba B1 cp ca cb C1 p
    = mkc_pw P ap A2 bp ba B2 cp ca cb C2 p
    -> A1 = A2 # B1 = B2 # C1 = C2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

Lemma isprog_vars_pw {p} :
  forall vs (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp, ba] B
    -> isprog_vars [cp, ca, cb] C
    -> isprog_vars vs p
    -> isprog_vars vs (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  allrw @isprog_eq.
  allrw @isprog_vars_eq; sp.

  simpl.
  allunfold @isprogram; repnd.
  allrw subvars_app_l; allrw remove_nvars_nil_l; allrw; sp;
  allrw subvars_prop; introv i; allrw in_remove_nvars; allrw in_single_iff;
  repnd; discover; allrw in_single_iff; sp.

  constructor; simpl; sp; subst; constructor; sp.
  allunfold @isprogram; sp.
Qed.

Definition mkc_pw_vs {p}
             (vs : list NVar)
             (P : @CTerm p)
             (ap : NVar) (A : CVTerm [ap])
             (bp : NVar) (ba : NVar) (B : CVTerm [bp, ba])
             (cp : NVar) (ca : NVar) (cb : NVar) (C : CVTerm [cp, ca, cb])
             (p : CVTerm vs) : CVTerm vs :=
  let (tP,wP) := P in
  let (tA,wA) := A in
  let (tB,wB) := B in
  let (tC,wC) := C in
  let (tp,wp) := p in
    exist (isprog_vars vs)
          (mk_pw tP ap tA bp ba tB cp ca cb tC tp)
          (isprog_vars_pw vs tP ap tA bp ba tB cp ca cb tC tp wP wA wB wC wp).

Definition mkc_pm {p}
           (P : @CTerm p)
           (ap : NVar) (A : CVTerm [ap])
           (bp : NVar) (ba : NVar) (B : CVTerm [bp, ba])
           (cp : NVar) (ca : NVar) (cb : NVar) (C : CVTerm [cp, ca, cb])
           (p : CTerm) : CTerm :=
  let (tP,wP) := P in
  let (tA,wA) := A in
  let (tB,wB) := B in
  let (tC,wC) := C in
  let (tp,wp) := p in
    exist isprog
          (mk_pm tP ap tA bp ba tB cp ca cb tC tp)
          (isprog_pm tP ap tA bp ba tB cp ca cb tC tp wP wA wB wC wp).

Lemma mkc_pm_eq1 {p} :
  forall (P1 : @CTerm p) ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2,
    mkc_pm P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
    = mkc_pm P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
    -> P1 = P2
       # p1 = p2
       # ap1 = ap2
       # bp1 = bp2
       # ba1 = ba2
       # cp1 = cp2
       # ca1 = ca2
       # cb1 = cb2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

Lemma mkc_pm_eq2 {p} :
  forall (P : @CTerm p) ap bp ba cp ca cb p A1 B1 C1 A2 B2 C2,
    mkc_pm P ap A1 bp ba B1 cp ca cb C1 p
    = mkc_pm P ap A2 bp ba B2 cp ca cb C2 p
    -> A1 = A2 # B1 = B2 # C1 = C2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.


Definition mkc_function {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_function a v b) (isprog_function a v b x y).
Definition mkw_function {p} (T1 : @WTerm p) (v : NVar) (T2 : WTerm) :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_function a v b) (wf_function a v b x y).

Lemma mkc_function_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_function a1 v1 b1 = mkc_function a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_function.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_function_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_function a v b1 = mkc_function a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_function.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_product {p} (T1 : @CTerm p) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_product a v b) (isprog_product a v b x y).
Definition mkw_product {p} (T1 : @WTerm p) (v : NVar) (T2 : WTerm) :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_product a v b) (wf_product a v b x y).

Lemma mkc_product_eq1 {p} :
  forall (a1 : @CTerm p) v1 b1 a2 v2 b2,
    mkc_product a1 v1 b1 = mkc_product a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold @mkc_product.
  inversion H; subst.
  eauto with pi.
Qed.
Lemma mkc_product_eq2 {p} :
  forall (a : @CTerm p) v b1 b2,
    mkc_product a v b1 = mkc_product a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold @mkc_product.
  inversion H; subst.
  eauto with pi.
Qed.

Definition mkc_var {p} (v : NVar) : @CVTerm p [v] :=
  exist (isprog_vars [v]) (mk_var v) (isprog_vars_var v).

Definition mkc_vsubtype {p} (T1 : @CTerm p) (v : NVar) (T2 : CTerm) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
  exist isprog (mk_vsubtype a v b) (isprog_vsubtype a v b x y).

Definition mkc_subtype {p} (T1 : @CTerm p) (T2 : CTerm) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
  exist isprog (mk_subtype a b) (isprog_subtype a b x y).

(** newvar on closed terms *)
Definition cnewvar {p} (t : @CTerm p) := newvar (proj1_sig t).

Lemma cnewvar_eq {p} :
  forall t : @CTerm p, cnewvar t = nvarx.
Proof.
  destruct t; unfold cnewvar, newvar; simpl.
  rw @isprog_eq in i.
  inversion i.
  unfold closed in H.
  rewrite H.
  unfold fresh_var; sp.
Qed.

Lemma isprog_vars_cvterm_var {p} :
  forall v : NVar,
  forall t : @CTerm p,
    isprog_vars [v] (proj1_sig t).
Proof.
  destruct t; unfold cnewvar.
  rw @isprog_vars_eq; simpl.
  rw @isprog_eq in i.
  inversion i; sp.
  unfold closed in H.
  rewrite H; sp.
Qed.

Lemma isprog_vars_cvterm_newvar {p} :
  forall t : @CTerm p,
    isprog_vars [cnewvar t] (proj1_sig t).
Proof.
  sp; apply isprog_vars_cvterm_var.
Qed.

(** Builds, from a closed term t, a term that has at most one free variable,
 * namely v, which we know not to be in t.
 * The term is the same.  Only the proof of closeness changes. *)
Definition cvterm_var {p} (v : NVar) (t : @CTerm p) : CVTerm [v] :=
  exist (isprog_vars [v])
        (proj1_sig t)
        (isprog_vars_cvterm_var v t).

Definition cvterm_newvar {p} (t : @CTerm p) : CVTerm [cnewvar t] :=
  cvterm_var (cnewvar t) t.

Lemma mk_cv_as_cvterm_var {p} :
  forall v (t : @CTerm p), mk_cv [v] t = cvterm_var v t.
Proof.
  intros.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Definition mkc_fun {p} (A B : @CTerm p) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_fun a b) (isprog_fun a b x y).

Lemma fold_mkc_fun {p} :
  forall (A B : @CTerm p),
    mkc_function A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_fun A B.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_ufun {p} (A B : @CTerm p) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_ufun a b) (isprog_ufun a b x y).

Lemma fold_mkc_ufun {p} :
  forall (A B : @CTerm p),
    mkc_isect A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_ufun A B.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_eufun {p} (A B : @CTerm p) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_eufun a b) (isprog_eufun a b x y).

Lemma fold_mkc_eufun {p} :
  forall (A B : @CTerm p),
    mkc_eisect A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_eufun A B.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_prod {p} (A B : @CTerm p) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_prod a b) (isprog_prod a b x y).

Lemma fold_mkc_prod {p} :
  forall (A B : @CTerm p),
    mkc_product A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_prod A B.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_iff {p} (a b : @CTerm p) := mkc_prod (mkc_fun a b) (mkc_fun b a).

Definition mkc_id {p} : @CTerm p := mkc_lam nvarx (mkc_var nvarx).

Definition mkc_squash {p} (T : @CTerm p) :=
  mkc_image T (mkc_lam nvarx (mk_cv [nvarx] mkc_axiom)).

Lemma get_cterm_mkc_squash {p} :
  forall T : @CTerm p, get_cterm (mkc_squash T) = mk_squash (get_cterm T).
Proof.
  intro; destruct_cterms; sp.
Qed.


Lemma isprogram_fix {p} :
  forall t : @NTerm p, isprogram t -> isprogram (mk_fix t).
Proof.
  introv isp.
  repeat constructor; simpl; sp; subst.
  unfold closed; simpl.
  rewrite remove_nvars_nil_l.
  rewrite app_nil_r.
  inversion isp as [cl w]; sp.
  inversion isp; sp.
Qed.

Lemma isprogram_fix_iff {p} :
  forall a : @NTerm p, isprogram a <=> isprogram (mk_fix a).
Proof.
  intros; split; intro i.
  apply isprogram_fix; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_fix {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_fix t).
Proof.
  intro; repeat (rw @isprog_eq); sp.
  apply isprogram_fix; sp.
Qed.

Lemma wf_fix {p} : forall t : @NTerm p, wf_term t -> wf_term (mk_fix t).
Proof.
  introv wt.
  allrw @wf_term_eq.
  constructor; simpl; sp; subst.
  constructor; auto.
Qed.

Lemma wf_bot {p} : @wf_term p mk_bot.
Proof.
  unfold mk_bot, mk_bottom.
  apply wf_fix.
  apply wf_id.
Qed.
Hint Immediate wf_bot : wf.

Lemma isprogram_bot {p} : @isprogram p mk_bot.
Proof.
  unfold mk_bot, mk_bottom.
  apply isprogram_fix.
  apply isprogram_lam; simpl.
  apply isprog_vars_var.
Qed.
Hint Immediate isprogram_bot.

Lemma isprogram_mk_bot {p} : @isprogram p mk_bot.
Proof.
  apply isprogram_bot.
Qed.
Hint Immediate isprogram_mk_bot.

Lemma isprog_bot {p} : @isprog p mk_bot.
Proof.
  rw @isprog_eq.
  apply isprogram_bot.
Qed.
Hint Immediate isprog_bot.

Lemma wf_vbot {p} : forall v, @wf_term p (mk_vbot v).
Proof.
  introv.
  unfold mk_vbot.
  apply wf_fix.
  apply wf_lam; sp.
Qed.
Hint Immediate wf_vbot : wf.

Lemma isprogram_vbot {p} : forall v, @isprogram p (mk_vbot v).
Proof.
  introv.
  unfold mk_vbot.
  apply isprogram_fix.
  apply isprogram_lam; simpl.
  apply isprog_vars_var.
Qed.
Hint Immediate isprogram_vbot.

Lemma isprog_vbot {p} : forall v, @isprog p (mk_vbot v).
Proof.
  introv.
  rw @isprog_eq.
  apply isprogram_vbot.
Qed.
Hint Immediate isprog_vbot.

Lemma isprogram_mk_false {p} :
  @isprogram p mk_false.
Proof.
  unfold mk_false.
  apply isprogram_approx.
  apply isprogram_axiom.
  apply isprogram_bot.
Qed.
Hint Immediate isprogram_mk_false.

Lemma isprog_mk_false {p} :
  @isprog p mk_false.
Proof.
  rw @isprog_eq.
  apply isprogram_mk_false.
Qed.

Lemma wf_mk_false {p} :
  @wf_term p mk_false.
Proof.
  sp.
Qed.

Definition mkc_false {p} : @CTerm p :=
  exist isprog mk_false isprog_mk_false.

Definition mkc_bot {p} : @CTerm p :=
  exist isprog mk_bot isprog_bot.

Definition mkc_fix {p} (t : @CTerm p) :=
  let (a,x) := t in
    exist isprog (mk_fix a) (isprog_fix a x).

Lemma mkc_bot_eq {p} :
  @mkc_bot p = mkc_fix mkc_id.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Lemma mkc_false_eq {p} :
  @mkc_false p = mkc_approx mkc_axiom mkc_bot.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Theorem isprogram_void {p} : @isprogram p mk_void.
Proof.
  unfold mk_void; apply isprogram_mk_false.
Qed.

Theorem isprog_void {p} : @isprog p mk_void.
Proof.
  unfold mk_void; apply isprog_mk_false.
Qed.

Theorem wf_void {p} : @wf_term p mk_void.
Proof.
  sp.
Qed.

Definition mkc_void {p} : @CTerm p := exist isprog mk_void isprog_void.

Definition mkc_unit {p} : @CTerm p := exist isprog mk_unit isprog_unit.

Lemma mkc_unit_eq {p} : @mkc_unit p = mkc_approx mkc_axiom mkc_axiom.
Proof.
  apply cterm_eq; auto.
Qed.

(*
Lemma isprogram_void_implies :
  forall bterms,
    isprogram (oterm (Can NVoid) bterms)
    -> bterms = [].
Proof.
  sp; allunfold isprogram; sp.
  inversion X; subst; allsimpl.
  allrw <- null_iff_nil; allsimpl.
  allrw null_map; sp.
Qed.
*)

Lemma fold_mkc_vsubtype {p} :
  forall (A : @CTerm p) v B,
    mkc_member mkc_id (mkc_function A v (cvterm_var v B))
    = mkc_vsubtype A v B.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Lemma fold_mkc_subtype {p} :
  forall (A B : @CTerm p),
    mkc_member mkc_id (mkc_function A (cnewvar B) (cvterm_newvar B))
    = mkc_subtype A B.
Proof.
  introv; destruct_cterms; apply cterm_eq; auto.
Qed.

Definition mkc_rec {p} (v : NVar) (t : @CVTerm p [v]) :=
  let (a,x) := t in
    exist isprog (mk_rec v a) (isprog_rec v a x).
Definition mkw_rec {p} (v : NVar) (t : @WTerm p) :=
  let (a,x) := t in
    exist wf_term (mk_rec v a) (wf_rec v a x).

Definition isvalue_wft {p} (t : @WTerm p) :=
  let (a,_) := t in isvalue a.

Definition isovalue_wft {p} (t : @WTerm p) :=
  let (a,_) := t in isovalue a.

Lemma isvalue_wft_mkw_approx {p} :
  forall t : @WTerm p, isvalue_wft (mkw_approx t t).
Proof.
  unfold isvalue_wft, mkw_approx; sp.
  destruct t; simpl.
  apply isvalue_approx.
Abort.

Lemma iscvalue_mkc_nat {p} : forall n : nat, @iscvalue p (mkc_nat n).
Proof.
  repeat constructor; sp; allsimpl; sp.
Qed.

Theorem iscvalue_mkc_uni {p} : forall i : nat, @iscvalue p (mkc_uni i).
Proof.
  repeat constructor; sp; allsimpl; sp.
Qed.

Lemma isvalue_wft_mkw_int {p} : @isvalue_wft p mkw_int.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma isovalue_wft_mkw_int {p} : @isovalue_wft p mkw_int.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma iscvalue_mkc_int {p} : @iscvalue p mkc_int.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma isovalue_wft_mkw_axiom {p} : @isovalue_wft p mkw_axiom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem iscvalue_mkc_axiom {p} : @iscvalue p mkc_axiom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem iscvalue_mkc_base {p} : @iscvalue p mkc_base.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Hint Immediate iscvalue_mkc_nat.
Hint Immediate iscvalue_mkc_uni.
Hint Immediate iscvalue_mkc_int.
Hint Immediate iscvalue_mkc_axiom.
Hint Immediate iscvalue_mkc_base.

Lemma isovalue_wft_mkw_approx {p} :
  forall t1 t2 : @WTerm p, isovalue_wft (mkw_approx t1 t2).
Proof.
  intro; destruct t1; destruct t2; simpl.
  apply isovalue_approx; allrw @nt_wf_eq; auto.
Qed.

Lemma iscvalue_mkc_approx {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_approx t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_approx; allrw @isprog_eq; auto.
Qed.

Lemma isovalue_wft_mkw_cequiv {p} :
  forall t1 t2 : @WTerm p, isovalue_wft (mkw_cequiv t1 t2).
Proof.
  intro; destruct t1; destruct t2; simpl.
  apply isovalue_cequiv; allrw @nt_wf_eq; auto.
Qed.

Lemma iscvalue_mkc_cequiv {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_cequiv t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_cequiv; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_texc {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_texc t1 t2).
Proof.
  introv; destruct_cterms; unfold iscvalue; simpl.
  apply isvalue_texc; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_union {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_union t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_union; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_eunion {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_eunion t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_eunion; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_union2 {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_union2 t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_union2; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_image {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_image t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_image; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_pertype {p} :
  forall t : @CTerm p, iscvalue (mkc_pertype t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_pertype; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_partial {p} :
  forall t : @CTerm p, iscvalue (mkc_partial t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_partial; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_ipertype {p} :
  forall t : @CTerm p, iscvalue (mkc_ipertype t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_ipertype; allrw @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_spertype {p} :
  forall t : @CTerm p, iscvalue (mkc_spertype t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_spertype; allrw @isprog_eq; auto.
Qed.

(*
Lemma iscvalue_mkc_tuni :
  forall t, iscvalue (mkc_tuni t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_tuni; allrw isprog_eq; auto.
Qed.
*)

(*
Lemma iscvalue_mkc_esquash :
  forall t, iscvalue (mkc_esquash t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_esquash; allrw isprog_eq; auto.
Qed.
*)

Lemma mkw_integer_eq_nat {p} :
  forall n,
    @mkw_integer p (Z.of_nat n) = mkw_nat n.
Proof.
  sp.
Qed.

Lemma iscvalue_mkc_equality {p} :
  forall t1 t2 T : @CTerm p, iscvalue (mkc_equality t1 t2 T).
Proof.
  intro; destruct t1; destruct t2; destruct T; unfold iscvalue; simpl.
  apply isvalue_equality; allrw @isprog_eq; auto.
  apply isprogram_equality; sp.
Qed.

Lemma isvalue_function {p} :
  forall (a : @NTerm p) v b, isprogram (mk_function a v b) -> isvalue (mk_function a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_product {p} :
  forall (a : @NTerm p) v b, isprogram (mk_product a v b) -> isvalue (mk_product a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_isect {p} :
  forall (a : @NTerm p) v b, isprogram (mk_isect a v b) -> isvalue (mk_isect a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_eisect {p} :
  forall (a : @NTerm p) v b, isprogram (mk_eisect a v b) -> isvalue (mk_eisect a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_disect {p} :
  forall (a : @NTerm p) v b, isprogram (mk_disect a v b) -> isvalue (mk_disect a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_set {p} :
  forall (a : @NTerm p) v b, isprogram (mk_set a v b) -> isvalue (mk_set a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_tunion {p} :
  forall (a : @NTerm p) v b, isprogram (mk_tunion a v b) -> isvalue (mk_tunion a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_w {p} :
  forall (a : @NTerm p) v b, isprogram (mk_w a v b) -> isvalue (mk_w a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_m {p} :
  forall (a : @NTerm p) v b, isprogram (mk_m a v b) -> isvalue (mk_m a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_pw {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprogram (mk_pw P ap A bp ba B cp ca cb C p)
    -> isvalue (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_pm {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprogram (mk_pm P ap A bp ba B cp ca cb C p)
    -> isvalue (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp; constructor; sp.
Qed.

Lemma implies_isvalue_function {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_function a v b).
Proof.
  sp.
  apply isvalue_function.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_function; sp.
Qed.

Lemma implies_isvalue_product {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_product a v b).
Proof.
  sp.
  apply isvalue_product.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_product; sp.
Qed.

Lemma implies_isvalue_isect {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_isect a v b).
Proof.
  sp.
  apply isvalue_isect.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_isect; sp.
Qed.

Lemma implies_isvalue_eisect {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_eisect a v b).
Proof.
  sp.
  apply isvalue_eisect.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_eisect; sp.
Qed.

Lemma implies_isvalue_disect {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_disect a v b).
Proof.
  sp.
  apply isvalue_disect.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_disect; sp.
Qed.

Lemma implies_isvalue_set {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_set a v b).
Proof.
  sp.
  apply isvalue_set.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_set; sp.
Qed.

Lemma implies_isvalue_tunion {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_tunion a v b).
Proof.
  sp.
  apply isvalue_tunion.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_tunion; sp.
Qed.

Lemma implies_isvalue_w {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_w a v b).
Proof.
  sp.
  apply isvalue_w.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_w; sp.
Qed.

Lemma implies_isvalue_m {p} :
  forall (a : @NTerm p) v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_m a v b).
Proof.
  sp.
  apply isvalue_m.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_m; sp.
Qed.

Lemma implies_isvalue_pw {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp,ba] B
    -> isprog_vars [cp,ca,cb] C
    -> isprog p
    -> isvalue (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  apply isvalue_pw.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_pw; sp.
Qed.

Lemma implies_isvalue_pm {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp,ba] B
    -> isprog_vars [cp,ca,cb] C
    -> isprog p
    -> isvalue (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  apply isvalue_pm.
  allrw @isprog_vars_eq; sp.
  allrw @isprog_eq.
  apply isprogram_pm; sp.
Qed.

Lemma iscvalue_mkc_function {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_function a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_function; sp.
Qed.
Hint Immediate iscvalue_mkc_function.

Lemma iscvalue_mkc_product {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_product a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_product; sp.
Qed.
Hint Immediate iscvalue_mkc_product.

Lemma iscvalue_mkc_isect {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_isect a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_isect; sp.
Qed.
Hint Immediate iscvalue_mkc_isect.

Lemma iscvalue_mkc_eisect {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_eisect a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_eisect; sp.
Qed.
Hint Immediate iscvalue_mkc_eisect.

Lemma iscvalue_mkc_disect {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_disect a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_disect; sp.
Qed.
Hint Immediate iscvalue_mkc_disect.

Lemma iscvalue_mkc_set {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_set a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_set; sp.
Qed.
Hint Immediate iscvalue_mkc_set.

Lemma iscvalue_mkc_tunion {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_tunion a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_tunion; sp.
Qed.
Hint Immediate iscvalue_mkc_tunion.

Lemma iscvalue_mkc_w {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_w a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_w; sp.
Qed.
Hint Immediate iscvalue_mkc_w.

Lemma iscvalue_mkc_m {p} :
  forall (a : @CTerm p) v b, iscvalue (mkc_m a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_m; sp.
Qed.
Hint Immediate iscvalue_mkc_m.

Lemma iscvalue_mkc_pw {p} :
  forall (P : @CTerm p) ap A bp ba B cp ca cb C p,
    iscvalue (mkc_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_pw; sp.
Qed.
Hint Immediate iscvalue_mkc_pw.

Lemma iscvalue_mkc_pm {p} :
  forall (P : @CTerm p) ap A bp ba B cp ca cb C p,
    iscvalue (mkc_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_pm; sp.
Qed.
Hint Immediate iscvalue_mkc_pm.



(* ---------------------------------------------------- *)


Definition list_rel {A} {B} (R : A -> B -> Prop) (ll : list A) (lr : list B) :=
  (length ll = length lr)
  #
  forall p1  p2 , LIn (p1, p2) (combine ll lr)
                  -> R p1 p2.

Definition default_nterm {o} : @NTerm o := mk_axiom.
Definition default_bt {o} : @BTerm o := bterm [] mk_axiom.

Definition bin_rel_nterm {o} := binrel_list (@default_nterm o).
Definition bin_rel_bterm {o} := binrel_list (@default_bt o).

(** gets the nth element of a list of bterms. if n is out of range, it returns the variable x
*)
Definition selectbt {p} (bts: list BTerm) (n:nat) : @BTerm p :=
  nth n bts default_bt.

(* Howe defines T(L) as B_0(L) (no bterm constructor)
  and T_0(L) as closed terms of T(L)
  so, a term T_0(L) cannot have the vterm constructor
 at the root
 This a superset of T_0(L)
*)
Inductive not_vbterm {p} : @NTerm p -> Type :=
  | nvbo : forall op bs, not_vbterm (oterm op bs).
Hint Constructors not_vbterm.

(** this should not be required anymore. a closed NTerm is automatically not_vbterm. Proof below*)
Definition not_vbtermb {p} (t : @NTerm p) : bool :=
  match t with
  | vterm _ => false
  | _ => true
  end.

Theorem closed_notvb {p} : forall t: @NTerm p , closed t -> not_vbterm t.
Proof.
  intros ? Hclose.
  destruct t; allsimpl; auto.
  unfold closed in Hclose. simpl in Hclose; ginv.
Qed.

Theorem selectbt_in {p} :
  forall n (bts : list (@BTerm p)),
    n < length bts -> LIn (selectbt bts n) bts.
Proof.
  intros. unfold selectbt.
  apply nth_in; auto.
Qed.

Lemma selectbt_cons {p} :
  forall (bt : @BTerm p) bts n,
    selectbt (bt :: bts) n = if beq_nat n 0 then bt else selectbt bts (n - 1).
Proof.
  unfold selectbt; simpl; sp.
  destruct n; simpl; sp.
  destruct n; simpl; sp.
Qed.

(*
Theorem isprogram_bt_iff : forall  (bt:BTerm ) , (isprogram_bt bt) <=>
forall (lnt : list NTerm) ,
    (forall nt: NTerm, (LIn nt lnt) -> isprogram nt)
   -> isprogram (apply_bterm  bt lnt ).
 intros. destruct bt as [lv nt].
 induction nt as [v| c bts] using NTerm_better_ind;
  [ Case_aux Case "vterm"
  | Case_aux Case "oterm"
  ].
 remember (memberb eq_var_dec v lv) as vinlv.
 destruct vinlv. fold assert () in Heqvinlv.
 sp_iff SCase.
  SCase "->".
   intros Hisp ? Hin.

*)




Lemma isvalue_wf {p} :
  forall c (bts : list (@BTerm p)),
    isvalue (oterm (Can c) bts)
    -> map num_bvars bts = OpBindings (Can c).
Proof. intros ? ?  Hval.
 inverts Hval as Hpr. inverts Hpr as Hclose Hwf.
 inverts Hwf; auto.
Qed.


Lemma isvalue_wf2 {p} : forall c (bts : list (@BTerm p)),
  (isvalue (oterm (Can c) bts))
  -> length bts= length(OpBindings (Can c)).
Proof. intros ? ?  Hval. apply isvalue_wf in Hval.
 (* fequalhyp H length.  why does this fail*)

 assert (length (map num_bvars bts) = length (OpBindings (Can c)))
   as Hlen by (rewrite Hval; reflexivity) .
 rewrite map_length in Hlen. auto.
Qed.


Lemma isprogram_wf3 {p} : forall o (bts : list (@BTerm p)),
  (isprogram (oterm o bts))
  -> forall n, (n<length bts) -> (num_bvars (selectbt bts n))= nth n (OpBindings o) 0.
Proof.
  intros ? ?  Hprog. apply isprogram_ot_iff  in Hprog. repnd.
  intros ? Hlt.
  assert(nth n (map num_bvars bts) 0= nth n (OpBindings o) 0)
    as Hnth by (rewrite Hprog0; reflexivity).
  unfold selectbt.
  instlemma (@map_nth
               BTerm nat num_bvars
               bts default_bt) as Hmapn.
  assert((@num_bvars p default_bt) = 0) as h by sp.
  rewrite h in Hmapn.
  rewrite Hmapn in Hnth. auto.
Qed.

Lemma isvalue_wf3 {p} : forall o (bts : list (@BTerm p)),
  (isvalue (oterm o bts))
  -> forall n, (n<length bts) -> (num_bvars (selectbt bts n))= nth n (OpBindings o) 0.
Proof.
  intros ? ?  Hval ? Hlt.
  inverts Hval as Hprog; apply @isprogram_wf3 with (n:=n) in Hprog; auto.
Qed.

Theorem var_not_prog {p} : forall v,  @isprogram p (vterm v) -> void.
Proof.
  unfold not. intros v Hpr.
  inversion Hpr as [Hclose ?].
  unfold closed in Hclose. simpl in Hclose. inversion Hclose.
Qed.

Lemma implies_isprogram_bt {p} :
  forall bts : list (@BTerm p),
    (forall l : BTerm, LIn l bts -> bt_wf l)
    -> flat_map free_vars_bterm bts = []
    -> forall bt : BTerm, LIn bt bts -> isprogram_bt bt.
Proof.
  intros bts Hbf Hflat ? Hin.
  unfold isprogram_bt, closed_bt; split; auto.
  rw flat_map_empty in Hflat. apply Hflat; auto.
Qed.

Theorem ntbf_wf {p} :
  forall nt : @NTerm p, (bt_wf (bterm [] nt)) -> nt_wf nt.
Proof.
  introv Hin. inverts Hin. auto.
Qed.

Lemma implies_isprogram_bt0 {p} :
  forall t : @NTerm p,
    isprogram t
    -> isprogram_bt (bterm [] t).
Proof.
  unfold isprogram_bt, closed_bt, isprogram, closed; simpl; sp.
Qed.

Theorem is_program_ot_bts0 {p} :
  forall o (nt : @NTerm p),
    isprogram nt
    -> OpBindings o = [0]
    -> isprogram (oterm o [bterm [] nt]).
Proof.
  introv Hpr Hop. allunfold @isprogram. repnd. split;auto. unfold closed. simpl.
  rewrite app_nil_r. rewrite remove_var_nil. sp.
  constructor; sp; allsimpl; sp; subst; sp.
Qed.

Theorem is_program_ot_nth_nobnd {p} :
  forall o (nt1 : @NTerm p) bts,
    isprogram (oterm o  bts)
    -> LIn (bterm [] nt1) bts
    -> isprogram nt1.
Proof. intros ? ? ? Hisp Hin. apply isprogram_ot_iff in Hisp. repnd.
  apply Hisp in Hin. inverts Hin as Hclose Hbf. inverts Hbf.
  unfold closed_bt in Hclose. simpl in Hclose.
  rewrite remove_var_nil in Hclose. split; auto.
Qed.

Theorem is_program_ot_fst_nobnd {p} :
  forall o (nt1 : @NTerm p) bts,
    isprogram (oterm o ((bterm [] nt1):: bts))
    -> isprogram nt1.
Proof.
  intros ? ? ? Hisp.
  apply @is_program_ot_nth_nobnd with (nt1:=nt1) in Hisp; sp.
Qed.

Theorem is_program_ot_snd_nobnd {p} :
  forall o bt1 (nt2 : @NTerm p) bts,
    isprogram (oterm o ((bt1)::(bterm [] nt2):: bts))
    -> isprogram nt2.
Proof. intros ? ? ? ? Hisp.
  apply is_program_ot_nth_nobnd with (nt1:=nt2) in Hisp; simpl; sp.
Qed.


Theorem is_program_ot_subst1 {p} :
  forall o (nt1 : @NTerm p) bts nt1r,
    isprogram (oterm o ((bterm [] nt1):: bts))
    -> isprogram nt1r
    -> isprogram (oterm o ((bterm [] nt1r):: bts)).
Proof. intros ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. unfold closed in Hclos. simpl in Hclos.
    apply app_eq_nil in Hclos. repnd.  rewrite remove_var_nil in Hclos0.
    inverts Hispst as Hclosst Hispst. unfold closed in Hclosst.
    rewrite remove_var_nil. rewrite Hclosst. rewrite Hclos. split;auto.
    invertsn Hisp. constructor;auto.
    intros ? Hin. inverts Hin. constructor; auto.
    apply Hisp. right; auto.
Qed.

Theorem is_program_ot_subst2 {p} :
  forall o bt1 (nt2 : @NTerm p) bts nt2r,
    isprogram (oterm o (bt1::(bterm [] nt2):: bts))
    -> isprogram nt2r
    -> isprogram (oterm o (bt1::(bterm [] nt2r):: bts)).
Proof. intros ? ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. inverts Hispst as Hclosst Hwfst.
    allunfold @closed. simpl.
    unfold closed in Hclos. allsimpl.
   simpl_vlist. rewrite Hclosst. rewrite Hclos0.
   simpl. split;auto.
   inverts Hisp as Hisp Hm. constructor;simpl; auto.
   intros ? Hin. dorn Hin;subst;auto. apply Hisp; auto.
   left; auto.
   dorn Hin; subst; auto.
   apply Hisp. right;right;auto.
Qed.


Theorem is_program_ot_nth_wf {p} :
  forall lv o (nt1 : @NTerm p) bts,
    isprogram (oterm o  bts)
    -> LIn (bterm lv nt1) bts
    -> nt_wf nt1.
Proof. intros ? ? ? ? Hisp Hin. apply isprogram_ot_iff in Hisp. repnd.
  assert (isprogram_bt (bterm lv nt1)) as Hass by (apply Hisp; auto).
  inverts Hass as Hass Hbt. inversion Hbt; auto.
Qed.

Lemma combine_vars_map_sp {p} :
  forall vars,
    combine vars (map vterm vars) = map (fun v => (v, @vterm p v)) vars.
Proof.
  induction vars; simpl; sp.
  rewrite IHvars; sp.
Qed.

Lemma combine_vars_map :
  forall A,
  forall f : NVar -> A,
  forall vars,
    combine vars (map f vars) = map (fun v => (v, f v)) vars.
Proof.
  induction vars; simpl; sp.
  rewrite IHvars; sp.
Qed.


Theorem in_selectbt {p} :
  forall (bt : @BTerm p) bts,
    LIn bt bts ->
    {n : nat $ n < length bts # selectbt bts n = bt}.
Proof.
  intros ? ? Hin. induction bts. inverts Hin.
  invertsn Hin.
  - exists 0. split; simpl; auto. omega.
  - destruct IHbts; auto. exists (S x). repnd.
    split; simpl; try omega. auto.
Qed.

(**useful for rewriting in complicated formulae*)
Theorem ntot_wf_iff {p} :
  forall o (bts : list (@BTerm p)),
    nt_wf (oterm o bts)
          <=> map num_bvars bts = OpBindings o
              # forall n : nat,
                  n < length bts -> bt_wf (selectbt bts n).
Proof. introv. sp_iff Case; introv H.
  Case "->". inverts H as Hbf Hmap. split; auto.
    introv Hlt. apply Hbf. apply selectbt_in; auto.
  Case "<-". repnd. constructor; auto.
    introv Hin. apply in_selectbt in Hin.
    exrepnd. rw <- Hin0;auto.
Qed.


Definition nvarxbt {p} : @BTerm p := bterm [] (vterm nvarx) .

Lemma wf_cvterm {p} :
  forall vs : list NVar,
  forall t : @CVTerm p vs,
    wf_term (get_cvterm vs t).
Proof.
  destruct t; simpl.
  rw @isprog_vars_eq in i; sp.
  rw @wf_term_eq; sp.
Qed.

Lemma isprogram_get_cterm {p} :
  forall a : @CTerm p, isprogram (get_cterm a).
Proof.
  destruct a; sp; simpl.
  rw @isprogram_eq; sp.
Qed.

Hint Immediate isprogram_get_cterm.

Lemma oterm_eq {p} :
  forall (o1 o2 : @Opid p) l1 l2,
    o1 = o2
    -> l1 = l2
    -> oterm o1 l1 = oterm o2 l2.
Proof.
  sp; allrw; sp.
Qed.

Lemma bterm_eq {p} :
  forall l1 l2 (n1 n2 : @NTerm p),
    l1 = l2
    -> n1 = n2
    -> bterm l1 n1 = bterm l2 n2.
Proof.
  sp; allrw; sp.
Qed.

Theorem selectbt_map {p} :
  forall lbt n (f: @BTerm p -> @BTerm p),
    n<length lbt
    -> selectbt (map f lbt) n = f (selectbt lbt n).
Proof.
  induction lbt; introv Hlt. inverts Hlt.
  simpl. destruct n; subst. reflexivity.
  allunfold @selectbt. allsimpl.
  assert (n < (length lbt)) by omega.
  auto.
Qed.


Theorem eq_maps_bt {p} :
  forall (B : Type) (f : BTerm -> B)
         (g : BTerm -> B) (la lc : list (@BTerm p)),
    length la = length lc
    -> (forall n : nat, n < length la
                        -> f (selectbt la n) = g (selectbt lc n))
    -> map f la = map g lc.
Proof. unfold selectbt. introv H2 H3. apply eq_maps2 in H3; auto.
Qed.

Lemma vterm_inj {p} : injective_fun (@vterm p).
Proof.
  introv Hf. inverts Hf. auto.
Qed.

Lemma map_eq_lift_vterm {p} :
  forall lvi lvo,
    map (@vterm p) lvi = map vterm lvo -> lvi = lvo.
Proof.
 intros.
  apply map_eq_injective with (f:=@vterm p); auto.
  exact vterm_inj.
Qed.

Fixpoint no_seq {o} (t : @NTerm o) : bool :=
  match t with
    | vterm _ => true
    | oterm op bs => no_seq_o op && ball (map no_seq_b bs)
  end
with no_seq_b {o} (b : @BTerm o) : bool :=
       match b with
         | bterm _ t => no_seq t
       end.

Lemma lin_lift_vterm {p} :
  forall v lv,
    LIn v lv <=> LIn (@vterm p v) (map vterm lv).
Proof.
  induction lv; [sp | ]. simpl.
  rw <- IHlv; split; intros hp; try (dorn hp); sp; subst; sp.
  inverts hp. sp.
Qed.

Definition all_vars_bt {p} (bt : @BTerm p) :=
  free_vars_bterm bt ++ bound_vars_bterm bt.

Lemma all_vars_ot {p} : forall (o : @Opid p) lbt, all_vars (oterm o lbt) =
  flat_map all_vars_bt lbt.
Proof.
  intros. unfold all_vars. simpl. unfold all_vars_bt.
Abort. (** they are only equal as bags*)


Theorem nil_remove_nvars_iff :
  forall l1 l2 : list NVar,
   (remove_nvars l1 l2) = [] <=> (forall x : NVar, LIn x l2 -> LIn x l1).
Proof.
  intros. rw <- null_iff_nil. apply null_remove_nvars.
Qed.

Theorem nil_rv_single_iff: forall lv v ,
   (remove_nvars lv [v]) = [] <=> (LIn v lv).
Proof.
  intros. rw <- null_iff_nil. rw null_remove_nvars.
  split; intro Hyp.
  apply Hyp. left. auto.
  introv Hin. apply in_list1 in Hin; subst; auto.
Qed.

Theorem selectbt_eq_in {p} :
  forall lv (nt : @NTerm p) lbt n,
  bterm lv nt = selectbt lbt n
  -> n < length lbt
  -> LIn (bterm lv nt) lbt.
Proof.
  introv Heq Hlt. rw Heq.
  apply selectbt_in; trivial.
Qed.

Lemma flat_map_closed_terms {p} :
  forall lnt : list (@NTerm p), lforall closed lnt
    -> flat_map free_vars lnt = [].
Proof.
  unfold lforall, closed. introv Hfr.
  apply flat_map_empty. trivial.
Qed.

Lemma flat_map_progs {p} :
  forall lnt : list (@NTerm p), lforall isprogram lnt
    -> flat_map free_vars lnt = [].
Proof.
  unfold lforall, closed. introv Hfr.
  apply flat_map_empty. introv Hin.
  apply Hfr in Hin. inverts Hin. auto.
Qed.

Theorem disjoint_lbt_bt {p} :
  forall vs lbt lv (nt : @NTerm p),
    disjoint vs (flat_map bound_vars_bterm lbt)
    -> LIn (bterm lv nt) lbt
    -> disjoint vs lv.
Proof.
  introv Hink1 Hin.
  apply disjoint_sym in Hink1; rw disjoint_flat_map_l in Hink1.
  apply Hink1 in Hin.
  simpl in Hin. rw disjoint_app_l in Hin.
  repnd; apply disjoint_sym. trivial.
Qed.

Tactic Notation "disjoint_reasoningv" :=
  (allunfold all_vars); repeat( progress disjoint_reasoning).

Lemma isprog_vars_top {p} :
  forall vs, @isprog_vars p vs mk_top.
Proof.
  intro; rw @isprog_vars_eq; simpl.
  repeat (rw remove_nvars_nil_l); repeat (rw app_nil_r); sp.
  rw @nt_wf_eq; sp.
Qed.
Hint Immediate isprog_vars_top.

Lemma isprog_vars_mk_false {p} :
  forall vs, @isprog_vars p vs mk_false.
Proof.
  intro; rw @isprog_vars_eq; simpl.
  repeat (rw remove_nvars_nil_l); repeat (rw app_nil_r); sp.
  rw @nt_wf_eq; sp.
Qed.
Hint Immediate isprog_vars_mk_false.

Definition selectnt {p} (n:nat) (lnt : list NTerm): @NTerm p :=
  nth n lnt (vterm nvarx).

Inductive nt_wf2 {p} : @NTerm p -> [univ] :=
  | wfvt2 : forall nv : NVar, nt_wf2 (vterm nv)
  | wfot2 : forall (o : Opid) (lnt : list BTerm),
            length lnt = length (OpBindings o)
           -> (forall n, n < (length lnt) ->
                num_bvars (selectbt lnt n) = nth n (OpBindings o) 0
                # bt_wf2 (selectbt lnt n))
           -> nt_wf2 (oterm o lnt)
  with bt_wf2 {p} : @BTerm p -> [univ] :=
    wfbt2 : forall (lnv : list NVar) (nt : NTerm),
              nt_wf2 nt -> bt_wf2 (bterm lnv nt).
Hint Constructors nt_wf2.

(** mainly for convenience in proofs *)
Theorem  selectbt_in2 {p} :
  forall (n : nat) (bts : list (@BTerm p)),
  n < length bts -> { bt : BTerm & (LIn bt bts # (selectbt bts n)=bt) }.
Proof.
  intros. exists (selectbt bts n).
  split;auto. apply selectbt_in; trivial.
Defined.

Lemma nt_wf_nt_wf2 {p} : forall t : @NTerm p, (nt_wf t) <=> (nt_wf2 t).
Proof.
  assert (0= num_bvars (bterm [] (@mk_axiom p))) as XX by auto.
  nterm_ind1 t as [|o lbt Hind] Case; split; introv Hyp; auto.

  - Case "oterm".
    inverts Hyp as Hl Hyp. constructor. apply_length Hyp;sp.
    introv hlt. unfold selectbt. rw <- Hyp.
    rw XX.
    rw map_nth; sp;[].
    fold (selectbt lbt n).
    pose proof (selectbt_in2 n lbt hlt) as Hbt.
    exrepnd. destruct bt as [lv nt].
    applydup Hind in Hbt1.
    rw Hbt0. constructor.
    apply Hl in Hbt1. inverts Hbt1.
    sp3.
  - inverts Hyp as Hl Hyp. constructor.
    + introv Hin. apply in_selectbt in Hin; auto;[].
      exrepnd. applydup Hyp in Hin1.
      rw Hin0 in Hin2. destruct l as [lv nt].
      constructor. exrepnd. invertsn Hin2.
      applysym @selectbt_in in Hin1. rw Hin0 in Hin1.
      apply Hind in Hin1. sp3.
    + eapply (tiff_snd (eq_list2 _ 0 _ _)). rw map_length.
      split; auto;[]. introv Hlt. apply Hyp in Hlt.
      repnd. rw <- Hlt0.
      rw XX. rw  map_nth. sp.
Qed.

Lemma isprog_vars_decide {p} :
  forall vs (a : @NTerm p) v1 a1 v2 a2,
    isprog_vars vs a
    -> isprog_vars (v1 :: vs) a1
    -> isprog_vars (v2 :: vs) a2
    -> isprog_vars vs (mk_decide a v1 a1 v2 a2).
Proof.
  introv ipa ipa1 ipa2.
  allrw @isprog_vars_eq; allsimpl.
  allrw subvars_eq.
  unfold subset in ipa, ipa1, ipa2; exrepd; sp.
  unfold subset; introv i.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff;
  allsimpl; sp;
  discover; sp; subst; sp.
  repeat (constructor; simpl; sp; subst).
Qed.

Lemma isprog_vars_spread {p} :
  forall vs (a : @NTerm p) v1 v2 b,
    isprog_vars vs a
    -> isprog_vars (v1 :: v2 :: vs) b
    -> isprog_vars vs (mk_spread a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allsimpl.
  allrw subvars_prop; repnd.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  dands.

  introv i.
  allrw in_app_iff.
  allrw in_remove_nvars; allsimpl.
  repdors; sp.
  allrw not_over_or; repnd.
  discover; sp.

  constructor; simpl; try (constructor).
  sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_vars_dsup {p} :
  forall vs (a : @NTerm p) v1 v2 b,
    isprog_vars vs a
    -> isprog_vars (v1 :: v2 :: vs) b
    -> isprog_vars vs (mk_dsup a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allsimpl.
  allrw subvars_prop; repnd.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  dands.

  introv i.
  allrw in_app_iff.
  allrw in_remove_nvars; allsimpl.
  repdors; sp.
  allrw not_over_or; repnd.
  discover; sp.

  constructor; simpl; try (constructor).
  sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_vars_cons {p} :
  forall v vs (t : @NTerm p), isprog_vars vs t -> isprog_vars (v :: vs) t.
Proof.
  introv ip.
  allrw @isprog_vars_eq.
  allrw subvars_eq; sp.
Qed.

Definition mkc_ite_vars {p} (vs : list NVar) (a b c : @CVTerm p vs) :=
  let (t1,x1) := a in
  let (t2,x2) := b in
  let (t3,x3) := c in
  exist (isprog_vars vs)
        (mk_decide t1 nvarx t2 nvarx t3)
        (isprog_vars_decide
           vs
           t1 nvarx t2 nvarx t3
           x1
           (isprog_vars_cons nvarx vs t2 x2)
           (isprog_vars_cons nvarx vs t3 x3)).

Definition mkc_lamc {p} v (t :@CTerm p) := mkc_lam v (mk_cv [v] t).

Theorem isvalue_inl {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_inl a).
Proof.
 intros; constructor; simpl; auto.
 fold (mk_inl a).
 apply isprogram_inl; auto.
Qed.

Lemma iscvalue_mkc_inl {p} :
  forall t : @CTerm p, iscvalue (mkc_inl t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_inl; allrw @isprog_eq; auto.
Qed.

Theorem isvalue_inr {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_inr a).
Proof.
 intros; constructor; simpl; auto. fold (mk_inr a).
 apply isprogram_inr; auto.
Qed.

Lemma iscvalue_mkc_inr {p} :
  forall t : @CTerm p, iscvalue (mkc_inr t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_inr; allrw @isprog_eq; auto.
Qed.

Theorem isvalue_sup {p} :
  forall a b : @NTerm p, isprogram a -> isprogram b -> isvalue (mk_sup a b).
Proof.
 intros; constructor; simpl; auto. fold (mk_sup a b).
 apply isprogram_sup; auto.
Qed.

Lemma iscvalue_mkc_sup {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_sup t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_sup; allrw @isprog_eq; auto.
Qed.

Theorem isvalue_refl {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_refl a).
Proof.
 intros; constructor; simpl; auto. fold (mk_refl a).
 apply isprogram_refl; auto.
Qed.
Hint Resolve isvalue_refl : slow.

Lemma iscvalue_mkc_refl {p} :
  forall t1 : @CTerm p, iscvalue (mkc_refl t1).
Proof.
  intro; destruct t1; unfold iscvalue; simpl.
  apply isvalue_refl; allrw @isprog_eq; auto.
Qed.
Hint Resolve iscvalue_mkc_refl : slow.

Definition is_inl {p} (t : @CTerm p) :=
  match get_cterm t with
    | vterm _ => false
    | oterm (Can (NInj NInl)) _ => true
    | oterm _ _ => false
  end.

Definition is_inr {p} (t : @CTerm p) :=
  match get_cterm t with
    | vterm _ => false
    | oterm (Can (NInj NInr)) _ => true
    | oterm _ _ => false
  end.

Lemma get_cterm_mkc_void {p} :
  get_cterm mkc_void = @mk_void p.
Proof.
  unfold mkc_void; simpl; sp.
Qed.

Lemma isvalue_mk_void {p} :
  @isvalue p mk_void.
Proof.
  apply isvalue_approx; sp.
Qed.
Hint Immediate isvalue_mk_void.


Definition mkc_idv {p} v : @CTerm p := mkc_lam v (mkc_var v).
Definition mkc_botv {p} v : @CTerm p := mkc_fix (mkc_idv v).
Definition mkc_voidv {p} v : @CTerm p := mkc_approx mkc_axiom (mkc_botv v).


Lemma wf_apply_iff {p} :
  forall a b : @NTerm p, (wf_term a # wf_term b) <=> wf_term (mk_apply a b).
Proof.
  introv; split; intro i.
  apply wf_apply; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)); intros k1 k2.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  inversion k1; subst.
  inversion k2; subst; sp.
Qed.

Lemma wf_apply2_iff {p} :
  forall a b c : @NTerm p,
    (wf_term a # wf_term b # wf_term c) <=> wf_term (mk_apply2 a b c).
Proof.
  introv.
  unfold mk_apply2.
  allrw <- @wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_apply {p} :
  forall (f a : @NTerm p) vs,
    isprog_vars vs (mk_apply f a) <=> (isprog_vars vs f # isprog_vars vs a).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_apply2 {p} :
  forall (f a b :@NTerm p) vs,
    isprog_vars vs (mk_apply2 f a b)
    <=>
    (isprog_vars vs f # isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  allrw <- @wf_term_eq.
  allrw <- @wf_apply2_iff; split; sp.
Qed.


Lemma wf_eapply_iff {p} :
  forall a b : @NTerm p, (wf_term a # wf_term b) <=> wf_term (mk_eapply a b).
Proof.
  introv; split; intro i.
  apply wf_eapply; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)); intros k1 k2.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  inversion k1; subst.
  inversion k2; subst; sp.
Qed.

Lemma isprog_vars_eapply {p} :
  forall (f a : @NTerm p) vs,
    isprog_vars vs (mk_eapply f a) <=> (isprog_vars vs f # isprog_vars vs a).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_eapply_iff; split; sp.
Qed.


(*
Lemma wf_apseq_iff {p} :
  forall f (a : @NTerm p), wf_term a <=> wf_term (mk_apseq f a).
Proof.
  introv; split; intro i.
  apply wf_apseq; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intros k1.
  repeat (dest_imp k1 hyp).
  inversion k1; subst; sp.
Qed.

Lemma isprog_vars_apseq {p} :
  forall f (a : @NTerm p) vs,
    isprog_vars vs (mk_apseq f a) <=> isprog_vars vs a.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_apseq_iff; split; sp.
Qed.
 *)

Lemma wf_parallel_iff {p} :
  forall (a b : @NTerm p),
    wf_term (mk_parallel a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro i; repnd; try (apply wf_parallel; complete sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl; clear i.
  pose proof (k (nobnd a)) as h1; autodimp h1 hyp.
  pose proof (k (nobnd b)) as h2; autodimp h2 hyp.
  allrw @bt_wf_iff; dands; auto.
Qed.

Lemma isprog_vars_parallel {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs (mk_parallel a b)
    <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw @nt_wf_eq.
  allrw @wf_parallel_iff.
  split; sp.
Qed.

Definition mkc_parallel {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_parallel a b) (isprog_parallel a b x y).

Lemma mkc_parallel_eq {p} :
  forall t1 t2 t3 t4 : @CTerm p,
    mkc_parallel t1 t2 = mkc_parallel t3 t4 -> t1 = t3 # t2 = t4.
Proof.
  introv e; destruct_cterms; allsimpl.
  inversion e; subst.
  irr; sp.
Qed.

Theorem wf_pertype_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_pertype a).
Proof.
  intros; split; intro i.
  apply wf_pertype; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_pertype {p} :
  forall (f : @NTerm p) vs,
    isprog_vars vs (mk_pertype f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_pertype_iff; split; sp.
Qed.

Theorem wf_partial_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_partial a).
Proof.
  intros; split; intro i.
  apply wf_partial; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_partial {p} :
  forall (f : @NTerm p) vs,
    isprog_vars vs (mk_partial f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_partial_iff; split; sp.
Qed.

Lemma isprog_vars_weak_l {p} :
  forall vs v (t : @NTerm p),
    isprog_vars vs t -> isprog_vars (snoc vs v) t.
Proof.
  introv i.
  allrw @isprog_vars_eq; sp.
  apply subvars_snoc_weak; sp.
Qed.

Lemma isprog_vars_weak_r {p} :
  forall vs v,
    isprog_vars (snoc vs v) (@mk_var p v).
Proof.
  introv.
  allrw @isprog_vars_eq; sp; allsimpl.
  rw subvars_singleton_l; rw in_snoc; sp.
Qed.
Hint Immediate isprog_vars_weak_r.

Lemma subset_snoc_swap_r :
  forall T vs vs1 vs2 (v : T),
    subset vs (snoc vs1 v ++ vs2)
    <=>
    subset vs (snoc (vs1 ++ vs2) v).
Proof.
  introv; unfold subset; split; intro s; introv i;
  apply s in i; allrw in_snoc; allrw in_app_iff; allrw in_snoc; sp.
Qed.

Lemma subvars_snoc_swap_r :
  forall vs vs1 vs2 v,
    subvars vs (snoc vs1 v ++ vs2)
    <=>
    subvars vs (snoc (vs1 ++ vs2) v).
Proof.
  introv.
  allrw subvars_eq.
  apply subset_snoc_swap_r; sp.
Qed.

Lemma isprog_vars_snoc_swap {p} :
  forall vs1 vs2 v (t : @NTerm p),
    isprog_vars (snoc vs1 v ++ vs2) t
    <=>
    isprog_vars (snoc (vs1 ++ vs2) v) t.
Proof.
  introv.
  allrw @isprog_vars_eq; split; intro i; repnd; sp.
  apply subvars_snoc_swap_r; sp.
  apply subvars_snoc_swap_r; sp.
Qed.

Lemma isprog_vars_lam {p} :
  forall vs v (b : @NTerm p),
    isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_lam v b).
Proof.
  introv ipv.
  allrw @isprog_vars_eq; simpl.
  rw app_nil_r.
  allrw subvars_prop; sp.
  allrw in_remove_nvars; allrw in_single_iff; allsimpl; sp.
  apply_in_hyp pp; sp.
  constructor; simpl; sp; subst.
  constructor; sp.
Qed.

Lemma isprog_vars_isect {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_isect a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_eisect {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_eisect a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_base {p} :
  forall vs, @isprog_vars p vs mk_base.
Proof.
  intros.
  rw @isprog_vars_eq; simpl; sp.
  constructor; simpl; sp.
Qed.
Hint Immediate isprog_vars_base.

Lemma isprog_vars_free_from_atom {p} :
  forall vs (a b T : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs T
    -> isprog_vars vs (mk_free_from_atom a b T).
Proof.
  introv ipa ipb ipt.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_efree_from_atom {p} :
  forall vs (a b T : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs T
    -> isprog_vars vs (mk_efree_from_atom a b T).
Proof.
  introv ipa ipb ipt.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_free_from_atoms {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_free_from_atoms a b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_free_from_defs {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_free_from_defs a b).
Proof.
  introv ipa ispb.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_equality {p} :
  forall vs (a b T : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs T
    -> isprog_vars vs (mk_equality a b T).
Proof.
  introv ipa ipb ipt.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_requality {p} :
  forall vs (a b T : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs T
    -> isprog_vars vs (mk_requality a b T).
Proof.
  introv ipa ipb ipt.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_tequality {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_tequality a b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_mk_var {p} :
  forall vs v, LIn v vs -> isprog_vars vs (@mk_var p v).
Proof.
  intros.
  rw @isprog_vars_eq; simpl; rw subvars_singleton_l; sp.
Qed.

Lemma isvalue_mk_unit {p} :
  @isvalue p mk_unit.
Proof.
  apply isvalue_approx; sp; apply isprogram_axiom.
Qed.
Hint Immediate isvalue_mk_unit.

Lemma mkc_void_eq_mkc_false {p} :
  @mkc_void p = mkc_false.
Proof.
  apply cterm_eq; auto.
Qed.

Lemma iscvalue_mkc_false {p} :
  @iscvalue p mkc_false.
Proof.
  unfold iscvalue, mkc_false; simpl; sp.
Qed.
Hint Immediate iscvalue_mkc_false.

Lemma isprogram_mk_true {p} :
  @isprogram p mk_true.
Proof.
  unfold mk_true.
  apply isprogram_approx.
  apply isprogram_axiom.
  apply isprogram_axiom.
Qed.
Hint Immediate isprogram_mk_true.

Lemma isprog_mk_true {p} :
  @isprog p mk_true.
Proof.
  rw @isprog_eq.
  apply isprogram_mk_true.
Qed.
Hint Immediate isprog_mk_true.

Definition mkc_true {p} : @CTerm p := exist isprog mk_true isprog_mk_true.

Lemma iscvalue_mkc_true {p} :
  @iscvalue p mkc_true.
Proof.
  unfold iscvalue, mkc_true; simpl; sp.
Qed.
Hint Immediate iscvalue_mkc_false.

Definition mkc_top {p} : @CTerm p :=
  mkc_isect mkc_false nvarx (mk_cv [nvarx] mkc_false).

Lemma get_cterm_mkc_top {p} :
  get_cterm mkc_top = @mk_top p.
Proof. sp. Qed.

Lemma mkc_true_eq {p} :
  @mkc_true p = mkc_approx mkc_axiom mkc_axiom.
Proof.
  apply cterm_eq; auto.
Qed.

Ltac rwselectbt :=
match goal with
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite <- H1 in H2
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite H1 in H2
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n  |-  context [selectbt ?lbt ?n] ] => rewrite <- H1
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  |-  context [selectbt ?lbt ?n] ] => rewrite H1
end.

Lemma bin_rel_nterm_if_combine {o} :
  forall (ts1 ts2 : list (@NTerm o)) R,
    (forall t1 t2, LIn (t1,t2) (combine ts1 ts2) -> R t1 t2)
    -> length ts1 = length ts2
    -> bin_rel_nterm R ts1 ts2.
Proof.
  unfold bin_rel_nterm, binrel_list; introv h e; dands; auto.
  introv k.
  apply h.
  rw <- combine_nth; auto.
  apply nth_in; auto.
  rw combine_length; rw <- e.
  rw Min.min_idempotent; auto.
Qed.

Theorem isprogram_ot_implies_eauto2 {p} :
  forall (o : @Opid p) bts,
    isprogram (oterm o bts)
    -> (forall n, n< length bts -> isprogram_bt (selectbt bts n)).
Proof.
  introv Hp Hlt. apply isprogram_ot_iff in Hp.
  apply selectbt_in in Hlt. exrepnd.
  eauto with slow.
Qed.


Lemma isprogram_bt_nobnd {p} :
  forall (t : @NTerm p),
    isprogram_bt (bterm [] t)
    -> isprogram (t).
Proof.
  unfold isprogram_bt, closed_bt, isprogram, closed; introns Hxx;  spc; allsimpl.
  inverts Hxx;sp.
Qed.

Lemma mkc_unit_eq_mkc_true {p} :
  @mkc_unit p = mkc_true.
Proof.
  apply cterm_eq; auto.
Qed.

Lemma free_vars_list_app {p} :
  forall (ts1 ts2 : list (@NTerm p)),
    free_vars_list (ts1 ++ ts2)
    = free_vars_list ts1 ++ free_vars_list ts2.
Proof.
  induction ts1; simpl; sp.
  rw IHts1; simpl.
  rw app_assoc; sp.
Qed.

Tactic Notation "ntermd" ident(h) "as" simple_intropattern(I)  ident(c) :=
  destruct h as I;
  [ Case_aux c "vterm"
  | Case_aux c "sterm"
  | Case_aux c "oterm"
  ].

Ltac prove_or :=
  try (left;cpx;fail);
  try (right;cpx;fail);
  try (left;left;cpx;fail);
  try (left;right;cpx;fail);
  try (right;left;cpx;fail);
  try (right;right;cpx;fail).

Ltac fold_selectbt :=
  match goal with
    | [ |- context [nth ?n ?lbt (bterm [] mk_axiom)] ] => fold (selectbt lbt n)
    | [ |- context [nth ?n ?lbt default_bt] ] => fold (selectbt lbt n)
  end.


Hint Resolve nt_wf_implies : slow.
Hint Resolve nt_wf_eq: slow.
Hint Resolve is_program_ot_nth_nobnd : slow.

Lemma isprog_ntwf_eauto {p} : forall t : @NTerm p, isprogram t -> nt_wf t.
Proof. unfold isprogram. spc.
Qed.
Hint Resolve isprog_ntwf_eauto : slow.

Theorem isprogram_ot_if_eauto {p} :
  forall (o : @Opid p) bts,
    map num_bvars bts = OpBindings o
    -> (forall bt, LIn bt bts -> isprogram_bt bt)
    -> isprogram (oterm o bts).
Proof.
 intros. apply isprogram_ot_iff;spc.
Qed.

Lemma isprogramd {p} :
  forall v,
    @isprogram p v
    -> {o : Opid $ {lbt : list BTerm $ v = oterm o lbt}}.
Proof.
  introv Hpr.
  invertsn Hpr.
  destruct v; inverts Hpr.
  eexists; eexists; eauto.
Qed.


Lemma isprogram_noncan {p} :
  forall v,
    @isprogram p v
    -> (isvalue v [+] isnoncan v [+] isexc v [+] isabs v).
Proof.
  introv Hp.
  applydup @isprogramd in Hp.
  repndors; exrepnd; subst; cpx.
  destruct o; cpx.
Qed.



(*
Ltac d_isnoncan H :=
  match type of H with
    isnoncan ?t => let tlbt := fresh t "lbt" in let tnc := fresh t "nc" in
              let tt := fresh "temp" in
              destruct t as [tt|tt tlbt];[inverts H as H; fail|];
              destruct tt as [tt|tnc]; [inverts H as H; fail|]
  end.
*)

Hint Resolve isprogram_fix : slow.

Lemma fold_combine : forall {A B} (v:A) (t:B),
  [(v,t)] = (combine [v] [t]).
Proof.
  intros. simpl. auto.
Qed.

Lemma nvarx_nvary : nvarx <> nvary.
Proof.
  allunfold nvarx.
  allunfold nvary.
  introv Hinc.
  inverts Hinc.
Qed.

Hint Immediate nvarx_nvary : slow.

Lemma noncan_not_value {p} :
  forall e : @NTerm p,
  isnoncan e
  -> isvalue e
  -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [|o lbt]; allsimpl; cpx.
  destruct o; cpx.
  inverts Hisv; allsimpl; tcsp.
Qed.

Theorem isprogram_ot_if_eauto2 {p} :
  forall (o : @Opid p) bts,
    map num_bvars bts = OpBindings o
    -> (forall n, n< length bts -> isprogram_bt (selectbt bts n))
    -> isprogram (oterm o bts).
Proof.
  introv Hn Hp. apply isprogram_ot_iff; dands; spcf.
  introv Hin. apply in_selectbt in Hin. exrepnd.
  eauto with slow.
  rw <- Hin0.
  eauto with slow.
Qed.

Hint Resolve isprogram_ot_if_eauto : slow.

Lemma newvars5_prop {p} :
  forall v1 v2 v3 v4 v5 (terms : list (@NTerm p)),
    (v1, v2, v3, v4, v5) = newvars5 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms ++ [v1])
       # !LIn v3 (free_vars_list terms ++ [v1, v2])
       # !LIn v4 (free_vars_list terms ++ [v1, v2, v3])
       # !LIn v5 (free_vars_list terms ++ [v1, v2, v3, v4]).
Proof.
  introv eq.
  unfold newvars5 in eq; cpx.
  unfold newvarlst; simpl; allrw @free_vars_list_app; simpl.
  dands; apply fresh_var_not_in.
Qed.

Lemma newvars5_prop2 {p} :
  forall v1 v2 v3 v4 v5 (terms : list (@NTerm p)),
    (v1, v2, v3, v4, v5) = newvars5 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms)
       # !LIn v3 (free_vars_list terms)
       # !LIn v4 (free_vars_list terms)
       # !LIn v5 (free_vars_list terms)
       # !v1 = v2
       # !v1 = v3
       # !v1 = v4
       # !v1 = v5
       # !v2 = v3
       # !v2 = v4
       # !v2 = v5
       # !v3 = v4
       # !v3 = v5
       # !v4 = v5.
Proof.
  introv eq.
  apply newvars5_prop in eq; repnd.
  allrw in_app_iff; allsimpl.
  repeat (apply not_over_or in eq; repnd).
  repeat (apply not_over_or in eq1; repnd).
  repeat (apply not_over_or in eq2; repnd).
  repeat (apply not_over_or in eq3; repnd).
  sp.
Qed.

Lemma newvars2_prop {p} :
  forall v1 v2 (terms : list (@NTerm p)),
    (v1, v2) = newvars2 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms ++ [v1]).
Proof.
  introv eq.
  unfold newvars2 in eq; cpx.
  unfold newvarlst; simpl; allrw @free_vars_list_app; simpl.
  dands; apply fresh_var_not_in.
Qed.

Lemma newvars2_prop2 {p} :
  forall v1 v2 (terms : list (@NTerm p)),
    (v1, v2) = newvars2 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms)
       # !v1 = v2.
Proof.
  introv eq.
  apply newvars2_prop in eq; repnd.
  allrw in_app_iff; allsimpl.
  repeat (apply not_over_or in eq; repnd).
  sp.
Qed.

Lemma newvars6_prop {p} :
  forall v1 v2 v3 v4 v5 v6 (terms : list (@NTerm p)),
    (v1, v2, v3, v4, v5, v6) = newvars6 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms ++ [v1])
       # !LIn v3 (free_vars_list terms ++ [v1, v2])
       # !LIn v4 (free_vars_list terms ++ [v1, v2, v3])
       # !LIn v5 (free_vars_list terms ++ [v1, v2, v3, v4])
       # !LIn v6 (free_vars_list terms ++ [v1, v2, v3, v4, v5]).
Proof.
  introv eq.
  unfold newvars6 in eq; cpx.
  unfold newvarlst; simpl; allrw @free_vars_list_app; simpl.
  dands; try (apply fresh_var_not_in).
Qed.

Lemma newvars6_prop2 {p} :
  forall v1 v2 v3 v4 v5 v6 (terms : list (@NTerm p)),
    (v1, v2, v3, v4, v5, v6) = newvars6 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms)
       # !LIn v3 (free_vars_list terms)
       # !LIn v4 (free_vars_list terms)
       # !LIn v5 (free_vars_list terms)
       # !LIn v6 (free_vars_list terms)
       # !v1 = v2
       # !v1 = v3
       # !v1 = v4
       # !v1 = v5
       # !v1 = v6
       # !v2 = v3
       # !v2 = v4
       # !v2 = v5
       # !v2 = v6
       # !v3 = v4
       # !v3 = v5
       # !v3 = v6
       # !v4 = v5
       # !v4 = v6
       # !v5 = v6.
Proof.
  introv eq.
  apply newvars6_prop in eq; repnd.
  allrw in_app_iff; allsimpl.
  repeat (apply not_over_or in eq; repnd).
  repeat (apply not_over_or in eq1; repnd).
  repeat (apply not_over_or in eq2; repnd).
  repeat (apply not_over_or in eq3; repnd).
  repeat (apply not_over_or in eq4; repnd).
  tcsp.
Qed.

Lemma newvarlst_prop {p} :
  forall (ts : list (@NTerm p)), ! LIn (newvarlst ts) (free_vars_list ts).
Proof.
  unfold newvarlst; sp.
  allapply fresh_var_not_in; sp.
Qed.

Lemma newvars7_prop {o} :
  forall (terms : list (@NTerm o)),
    {v1 : NVar
     & {v2 : NVar
     & {v3 : NVar
     & {v4 : NVar
     & {v5 : NVar
     & {v6 : NVar
     & {v7 : NVar
     & (v1,v2,v3,v4,v5,v6,v7) = newvars7 terms
     # !LIn v1 (free_vars_list terms)
     # !LIn v2 (free_vars_list terms)
     # !LIn v3 (free_vars_list terms)
     # !LIn v4 (free_vars_list terms)
     # !LIn v5 (free_vars_list terms)
     # !LIn v6 (free_vars_list terms)
     # !LIn v7 (free_vars_list terms)

     # !v1 = v2
     # !v1 = v3
     # !v1 = v4
     # !v1 = v5
     # !v1 = v6
     # !v1 = v7

     # !v2 = v3
     # !v2 = v4
     # !v2 = v5
     # !v2 = v6
     # !v2 = v7

     # !v3 = v4
     # !v3 = v5
     # !v3 = v6
     # !v3 = v7

     # !v4 = v5
     # !v4 = v6
     # !v4 = v7

     # !v5 = v6
     # !v5 = v7

     # !v6 = v7}}}}}}}.
Proof.
  introv.
  remember (newvars7 terms) as nv; sp.
  sp.
  unfold newvars7 in Heqnv.
  remember (newvars6 terms) as nv'; sp.
  apply newvars6_prop2 in Heqnv'; repnd.
  ginv.
  pose proof (newvarlst_prop
                (terms ++
                       [mk_var nv'4, mk_var nv'3,
                        mk_var nv'2, mk_var nv'1,
                        mk_var nv'0, mk_var nv'])) as h.
  remember (newvarlst
              (terms ++
                     [mk_var nv'4, mk_var nv'3,
                      mk_var nv'2, mk_var nv'1,
                      mk_var nv'0, mk_var nv'])) as n.
  clear Heqn.
  allrw @free_vars_list_app; allsimpl.
  allrw in_app_iff; allsimpl.
  allrw not_over_or; repnd; GC.
  eexists; eexists; eexists; eexists; eexists; eexists; eexists.
  dands; eauto.
Qed.

Lemma mkc_inl_inr_eq {p} :
  forall a b : @CTerm p, mkc_inl a = mkc_inr b -> False.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H.
Qed.

Lemma mkc_inr_inl_eq {p} :
  forall a b : @CTerm p, mkc_inr a = mkc_inl b -> False.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H.
Qed.

Lemma closed_implies {p} :
  forall t : @NTerm p,
    closed t -> (forall x, !LIn x (free_vars t)).
Proof.
  introv cl i; rw cl in i; sp.
Qed.

Lemma closed_iff {p} :
  forall t : @NTerm p,
    closed t <=> (forall x, !LIn x (free_vars t)).
Proof.
  introv; split; intro k.
  - apply closed_implies; auto.
  - unfold closed.
    apply subvars_nil_r.
    rw subvars_prop; introv i.
    apply k in i; sp.
Qed.

Lemma isprog_lam_iff {p} :
  forall v (b : @NTerm p),
    isprog_vars [v] b <=> isprog (mk_lam v b).
Proof.
  introv; split; intro k.
  apply isprog_lam; sp.
  allrw @isprog_eq.
  rw @isprog_vars_eq.
  unfold isprogram in k; repnd.
  inversion k as [| o lnt j meq ]; allsimpl; subst.
  generalize (j (bterm [v] b)); intro u; dest_imp u hyp.
  inversion u; subst; sp.
  generalize (closed_implies (mk_lam v b) k0); intro i.
  rw subvars_prop; introv y.
  allsimpl.
  destruct (eq_var_dec v x); sp.
  allrw app_nil_r.
  generalize (i x); intro pp.
  allrw in_remove_nvars; allrw in_single_iff.
  provefalse.
  apply pp; sp.
Qed.

Lemma isprog_vars_lam_iff {p} :
  forall v (b : @NTerm p) vs,
    isprog_vars vs (mk_lam v b) <=> isprog_vars (vs ++ [v]) b.
Proof.
  introv; split; intro k; allrw @isprog_vars_eq; allrw @nt_wf_eq; repnd; dands;
  allrw <- @wf_lam_iff; try (complete sp); allsimpl; allrw app_nil_r; allrw subvars_prop;
  introv i.

  rw in_app_iff; rw in_single_iff.
  destruct (eq_var_dec v x); sp.
  generalize (k0 x).
  rw in_remove_nvars; rw in_single_iff; intro j.
  dest_imp j hyp.

  rw in_remove_nvars in i; rw in_single_iff in i; repnd.
  generalize (k0 x); intro j; dest_imp j hyp.
  rw in_app_iff in j; rw in_single_iff in j; sp.
Qed.

Lemma isprog_vars_isect_iff {p} :
  forall vs (a : @NTerm p) v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_isect a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_isect; sp.
  allrw @isprog_vars_eq; allrw @nt_wf_eq.
  allrw <- @wf_isect_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_eisect_iff {p} :
  forall vs (a : @NTerm p) v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_eisect a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_eisect; sp.
  allrw @isprog_vars_eq; allrw @nt_wf_eq.
  allrw <- @wf_eisect_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_free_from_atom_iff {p} :
  forall vs (a b T : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b # isprog_vars vs T)
    <=> isprog_vars vs (mk_free_from_atom a b T).
Proof.
  introv; split; intro k.
  - apply isprog_vars_free_from_atom; sp.
  - allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw <- @wf_free_from_atom_iff.
    allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_efree_from_atom_iff {p} :
  forall vs (a b T : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b # isprog_vars vs T)
    <=> isprog_vars vs (mk_efree_from_atom a b T).
Proof.
  introv; split; intro k.
  - apply isprog_vars_efree_from_atom; sp.
  - allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw <- @wf_efree_from_atom_iff.
    allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_free_from_atoms_iff {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_free_from_atoms a b).
Proof.
  introv; split; intro k.
  - apply isprog_vars_free_from_atoms; sp.
  - allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw <- @wf_free_from_atoms_iff.
    allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_free_from_defs_iff {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_free_from_defs a b).
Proof.
  introv; split; intro k.
  - apply isprog_vars_free_from_defs; sp.
  - allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw <- @wf_free_from_defs_iff.
    allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_equality_iff {p} :
  forall vs (a b T : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b # isprog_vars vs T)
    <=> isprog_vars vs (mk_equality a b T).
Proof.
  introv; split; intro k.
  apply isprog_vars_equality; sp.
  allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw <- @wf_equality_iff.
  allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_requality_iff {p} :
  forall vs (a b T : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b # isprog_vars vs T)
    <=> isprog_vars vs (mk_requality a b T).
Proof.
  introv; split; intro k.
  apply isprog_vars_requality; sp.
  allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw <- @wf_requality_iff.
  allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_tequality_iff {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_tequality a b).
Proof.
  introv; split; intro k.
  apply isprog_vars_tequality; sp.
  allrw @isprog_vars_eq; allsimpl; allrw @nt_wf_eq.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw <- @wf_tequality_iff.
  allrw subvars_app_l; sp.
Qed.

Theorem isprog_pertype_iff {p} :
  forall a : @NTerm p, isprog a <=> isprog (mk_pertype a).
Proof.
  introv; split; intro k.
  apply isprog_pertype; sp.
  allrw @isprog_eq; allunfold @isprogram; allrw @nt_wf_eq.
  allrw <- @wf_pertype_iff; sp.
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma isprog_vars_base_iff {p} :
  forall vs, @isprog_vars p vs mk_base <=> True.
Proof.
  intros.
  rw @isprog_vars_eq; simpl; sp; split; sp.
  constructor; simpl; sp.
Qed.

Lemma isprog_vars_app1 {p} :
  forall (t : @NTerm p) vs1 vs2,
    isprog_vars vs1 t
    -> isprog_vars (vs1 ++ vs2) t.
Proof.
  sp; alltrewrite @isprog_vars_eq; sp.
  alltrewrite subvars_eq.
  apply subset_app_r; sp.
Qed.

Lemma isprog_vars_cons_if2 {p} :
  forall v vs (t : @NTerm p),
    isprog_vars (v :: vs) t
    -> !LIn v (free_vars t)
    -> isprog_vars vs t.
Proof.
  introv ip ni.
  allrw @isprog_vars_eq.
  allrw subvars_prop; sp.
  discover; allsimpl; sp; subst; sp.
Qed.

Lemma isprog_vars_cons_app1 {p} :
  forall vs1 vs2 (t : @NTerm p),
    isprog_vars (vs1 ++ vs2) t
    -> (forall v, LIn v vs2 -> !LIn v (free_vars t))
    -> isprog_vars vs1 t.
Proof.
  introv ip ni.
  allrw @isprog_vars_eq.
  allrw subvars_prop; sp.
  discover.
  allrw in_app_iff; sp.
  discover; sp.
Qed.

Ltac unfold_all_mk :=
       allunfold mk_apply
       ;allunfold mk_eapply
(*       ;allunfold mk_apseq*)
       ;allunfold mk_parallel
       ;allunfold mk_bottom
       ;allunfold mk_fix
       ;allunfold mk_id
       ;allunfold mk_lam
       ;allunfold mk_var
       ;allunfold mk_free_from_atom
       ;allunfold mk_efree_from_atom
       ;allunfold mk_free_from_atoms
       ;allunfold mk_free_from_defs
       ;allunfold mk_equality
       ;allunfold mk_requality
       ;allunfold mk_tequality
       ;allunfold mk_cequiv
       ;allunfold mk_inl
       ;allunfold mk_inr
       ;allunfold mk_pair
       ;allunfold mk_sup
       ;allunfold mk_refl
       ;allunfold mk_int
       ;allunfold mk_uni
       ;allunfold mk_base
       ;allunfold mk_fun
       ;allunfold mk_set
       ;allunfold mk_texc
       ;allunfold mk_tunion
       ;allunfold mk_quotient
       ;allunfold mk_isect
       ;allunfold mk_disect
       ;allunfold mk_w
       ;allunfold mk_m
       ;allunfold mk_pw
       ;allunfold mk_pm
       ;allunfold mk_pertype
       ;allunfold mk_ipertype
       ;allunfold mk_spertype
       ;allunfold mk_tuni
       ;allunfold mk_partial
       ;allunfold mk_union
       ;allunfold mk_eunion
       ;allunfold mk_union2
       ;allunfold mk_approx
       ;allunfold mk_cequiv
       ;allunfold mk_compute
       ;allunfold mk_rec
       ;allunfold mk_image
       ;allunfold mk_admiss
       ;allunfold mk_mono
       ;allunfold nobnd.

Lemma isprogram_inl_iff {p} :
  forall a : @NTerm p, isprogram a <=> isprogram (mk_inl a).
Proof.
  intros; split; intro i.
  apply isprogram_inl; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprogram_inr_iff {p} :
  forall a : @NTerm p, isprogram a <=> isprogram (mk_inr a).
Proof.
  intros; split; intro i.
  apply isprogram_inr; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprogram_texc_iff {p} :
  forall a b : @NTerm p,
    (isprogram a # isprogram b) <=> isprogram (mk_texc a b).
Proof.
  intros; split; intro i.
  apply isprogram_texc; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_union_iff {p} :
  forall a b : @NTerm p, (isprogram a # isprogram b) <=> isprogram (mk_union a b).
Proof.
  intros; split; intro i.
  apply isprogram_union; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_eunion_iff {p} :
  forall a b : @NTerm p, (isprogram a # isprogram b) <=> isprogram (mk_eunion a b).
Proof.
  intros; split; intro i.
  apply isprogram_eunion; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_union2_iff {p} :
  forall a b : @NTerm p, (isprogram a # isprogram b) <=> isprogram (mk_union2 a b).
Proof.
  intros; split; intro i.
  apply isprogram_union2; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_m_iff {p} :
  forall (a : @NTerm p) v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_m a v b).
Proof.
  introv; split; intro k; try (apply isprog_m; sp).
  allrw @isprog_eq; allrw @isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [pp]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in pp; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma isprogram_pair_iff {p} :
  forall a b : @NTerm p, (isprogram a # isprogram b) <=> isprogram (mk_pair a b).
Proof.
  intros; split; intro i.
  apply isprogram_pair; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Definition mkc_admiss {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
  exist isprog (mk_admiss a) (isprog_admiss a x).

Theorem isvalue_admiss {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_admiss a).
Proof.
 intros; constructor; simpl; auto; apply isprogram_admiss; auto.
Qed.

Lemma iscvalue_mkc_admiss {p} :
  forall t : @CTerm p, iscvalue (mkc_admiss t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_admiss; allrw @isprog_eq; auto.
Qed.

Definition mkc_mono {p} (R : @CTerm p) : CTerm :=
  let (a,x) := R in
  exist isprog (mk_mono a) (isprog_mono a x).

Theorem isvalue_mono {p} :
  forall a : @NTerm p, isprogram a -> isvalue (mk_mono a).
Proof.
 intros; constructor; simpl; auto; apply isprogram_mono; auto.
Qed.

Lemma iscvalue_mkc_mono {p} :
  forall t : @CTerm p, iscvalue (mkc_mono t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_mono; allrw @isprog_eq; auto.
Qed.

Lemma wf_cequiv_iff {p} :
  forall a b : @NTerm p, (wf_term a # wf_term b) <=> wf_term (mk_cequiv a b).
Proof.
  sp; split; intros k.
  apply wf_cequiv; sp.
  allrw @wf_term_eq.
  inversion k as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)); generalize (i (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  inversion i1; inversion i2; sp.
Qed.

Definition mkc_or {p} (A B : @CTerm p) := mkc_union A B.
Definition mkc_eor {p} (A B : @CTerm p) := mkc_eunion A B.
Definition mkc_not {p} (P : @CTerm p) := mkc_fun P mkc_void.

Definition mkc_btrue {o} : @CTerm o := mkc_inl mkc_axiom.
Definition mkc_bfalse {o} : @CTerm o := mkc_inr mkc_axiom.

Lemma wf_fun {p} :
  forall A B : @NTerm p, wf_term (mk_fun A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw @wf_term_eq in w.
  inversion w as [| o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.

  rw <- @nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_ufun {p} :
  forall A B : @NTerm p, wf_term (mk_ufun A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw @wf_term_eq in w.
  inversion w as [| o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.

  rw <- @nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_eufun {p} :
  forall A B : @NTerm p, wf_term (mk_eufun A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw @wf_term_eq in w.
  inversion w as [| o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.

  rw <- @nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_prod {p} :
  forall A B : @NTerm p, wf_term (mk_prod A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw @wf_term_eq in w.
  inversion w as [| o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.

  rw <- @nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_not {p} :
  forall A : @NTerm p, wf_term (mk_not A) <=> wf_term A.
Proof.
  introv.
  rw @wf_fun; split; sp.
Qed.

Lemma wf_subtype_rel {p} :
  forall a b : @NTerm p,
    wf_term a
    -> wf_term b
    -> wf_term (mk_subtype_rel a b).
Proof.
  sp; unfold mk_subtype_rel.
  apply wf_member; sp.
  apply wf_fun; sp.
Qed.

Lemma wf_fun_iff {p} :
  forall (a b : @NTerm p),
    wf_term (mk_fun a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_fun.
  rw <- @wf_function_iff; sp.
Qed.

Lemma wf_subtype_rel_iff {p} :
  forall a b : @NTerm p,
    wf_term (mk_subtype_rel a b) <=> (wf_term a # wf_term b).
Proof.
  sp; split; intro.
  - unfold mk_subtype_rel in H.
    allrw <- @wf_member_iff; repd.
    allrw @wf_fun_iff; sp.
  - apply wf_subtype_rel; sp.
Qed.

Lemma isprog_subtype_rel {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_subtype_rel a b).
Proof.
  unfold mk_subtype_rel; introv ispa ispb.
  apply isprog_member; auto.
  apply isprog_fun; auto.
Qed.

Definition mkc_subtype_rel {p} (T1 T2 : @CTerm p) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
  exist isprog (mk_subtype_rel a b) (isprog_subtype_rel a b x y).

Ltac destruct_bterms :=
  repeat match goal with
             [bt : BTerm |- _] =>
             let btlv := fresh bt "lv" in
             let btnt := fresh bt "nt" in
             destruct bt as [btlv btnt]
         end.

Lemma mkc_admiss_eq {p} :
  forall T1 T2 : @CTerm p, mkc_admiss T1 = mkc_admiss T2 -> T1 = T2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.

Lemma mkc_mono_eq {p} :
  forall T1 T2 : @CTerm p, mkc_mono T1 = mkc_mono T2 -> T1 = T2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  eauto with pi.
Qed.



Lemma wf_less {p} :
  forall a b c d : @NTerm p,
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> wf_term (mk_less a b c d).
Proof.
  introv; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntc ntd; inversion nta; inversion ntb; inversion ntc; inversion ntd; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_less_iff {p} :
  forall a b c d : @NTerm p,
    (wf_term a # wf_term b # wf_term c # wf_term d) <=> wf_term (mk_less a b c d).
Proof.
  introv; split; intro i.
  apply wf_less; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)) (k (nobnd d)); intros k1 k2 k3 k4.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  repeat (dest_imp k3 hyp).
  repeat (dest_imp k4 hyp).
  inversion k1; subst.
  inversion k2; subst.
  inversion k3; subst.
  inversion k4; subst; sp.
Qed.

Lemma isprog_vars_less {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_less a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_less_iff; split; sp.
Qed.

Lemma isprog_vars_function {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_function a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_function_iff {p} :
  forall vs (a : @NTerm p) v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_function a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_function; sp.
  allrw @isprog_vars_eq; allrw @nt_wf_eq.
  allrw <- @wf_function_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_cons_newvar {p} :
  forall (b : @NTerm p) vs,
    isprog_vars (newvar b :: vs) b <=> isprog_vars vs b.
Proof.
  introv; split; intro k.

  allrw @isprog_vars_eq.
  allrw subvars_prop; repnd; dands; auto.
  introv i.
  applydup k0 in i; simpl in i0; repdors; subst; auto.
  apply newvar_prop in i; sp.

  apply isprog_vars_cons; sp.
Qed.

Lemma isprog_vars_fun {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_fun a b).
Proof.
  introv.
  rw <- @isprog_vars_function_iff.
  rw @isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_ufun {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_ufun a b).
Proof.
  introv.
  rw <- @isprog_vars_isect_iff.
  rw @isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_eufun {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_eufun a b).
Proof.
  introv.
  rw <- @isprog_vars_eisect_iff.
  rw @isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_product {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_product a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Theorem wf_product_iff {p} :
  forall (a : @NTerm p) v b, (wf_term a # wf_term b) <=> wf_term (mk_product a v b).
Proof.
  sp; split; intro i; try (apply wf_product; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_vars_product_iff {p} :
  forall vs (a : @NTerm p) v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_product a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_product; sp.
  allrw @isprog_vars_eq; allrw @nt_wf_eq.
  allrw <- @wf_product_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_prod {p} :
  forall vs (a b : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_prod a b).
Proof.
  introv.
  rw <- @isprog_vars_product_iff.
  rw @isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_set {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_set a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_set_iff {p} :
  forall vs (a : @NTerm p) v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_set a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_set; sp.
  allrw @isprog_vars_eq; allrw @nt_wf_eq.
  allrw <- @wf_set_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_tunion {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_tunion a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_tunion_iff {p} :
  forall vs (a : @NTerm p) v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_tunion a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_tunion; sp.
  allrw @isprog_vars_eq; allrw @nt_wf_eq.
  allrw <- @wf_tunion_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_void_iff {p} :
  forall vs, @isprog_vars p vs mk_void <=> True.
Proof.
  introv; split; intro k; auto.
Qed.

Lemma isprog_vars_true_iff {p} :
  forall vs, @isprog_vars p vs mk_true <=> True.
Proof.
  introv; split; intro k; auto.
  rw @isprog_vars_eq; sp.
  constructor; sp.
  allsimpl; sp; subst; repeat constructor; simpl; sp.
Qed.

Lemma isprog_vars_false_iff {p} :
  forall vs, @isprog_vars p vs mk_false <=> True.
Proof.
  introv; split; intro k; auto.
Qed.

Lemma isprog_vars_le {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs (mk_le a b) <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv; unfold mk_le.
  rw <- @isprog_vars_fun.
  rw @isprog_vars_void_iff.
  rw @isprog_vars_less.
  rw @isprog_vars_false_iff.
  rw @isprog_vars_true_iff.
  split; sp.
Qed.

Lemma isprog_vars_zero {p} :
  forall vs,
    @isprog_vars p vs mk_zero.
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; tcsp.
  constructor; simpl; tcsp.
Qed.
Hint Resolve isprog_vars_zero : slow.

Lemma isprog_tnat {p} : @isprog p mk_tnat.
Proof.
  rw <- @isprog_set_iff.
  dands; auto.
  rw @isprog_vars_le; dands; eauto 3 with slow.
  apply isprog_vars_var.
Qed.

Definition mkc_tnat {p} : @CTerm p := exist isprog mk_tnat isprog_tnat.

Lemma free_vars_fun {p} :
  forall a b : @NTerm p, free_vars (mk_fun a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r.
  assert (disjoint (free_vars b) [newvar b]) as disj.
  apply disjoint_sym.
  rw disjoint_singleton_l.
  apply newvar_prop.
  rw remove_nvars_unchanged in disj.
  rw disj; auto.
Qed.

Lemma free_vars_ufun {p} :
  forall a b : @NTerm p, free_vars (mk_ufun a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r.
  assert (disjoint (free_vars b) [newvar b]) as disj.
  apply disjoint_sym.
  rw disjoint_singleton_l.
  apply newvar_prop.
  rw remove_nvars_unchanged in disj.
  rw disj; auto.
Qed.

Lemma free_vars_eufun {p} :
  forall a b : @NTerm p, free_vars (mk_eufun a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r.
  assert (disjoint (free_vars b) [newvar b]) as disj.
  apply disjoint_sym.
  rw disjoint_singleton_l.
  apply newvar_prop.
  rw remove_nvars_unchanged in disj.
  rw disj; auto.
Qed.

Lemma isprogram_mk_zero {p} :
  @isprogram p mk_zero.
Proof.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_mk_zero.

Lemma isprogram_mk_one {p} :
  @isprogram p mk_one.
Proof.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_mk_one.

Lemma isprog_mk_zero {p} :
  @isprog p mk_zero.
Proof.
  rw @isprog_eq.
  apply isprogram_mk_zero.
Qed.
Hint Immediate isprog_mk_zero.

Definition mkc_zero {p} : @CTerm p := exist isprog mk_zero isprog_mk_zero.

Definition mk_eta_pair {p} (t : @NTerm p) := mk_pair (mk_pi1 t) (mk_pi2 t).
Definition mk_eta_inl {p} (t : @NTerm p) := mk_inl (mk_outl t).
Definition mk_eta_inr {p} (t : @NTerm p) := mk_inr (mk_outr t).

Lemma free_vars_mk_pertype {p} :
  forall A : @NTerm p,
    free_vars (mk_pertype A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma free_vars_mk_ipertype {p} :
  forall A : @NTerm p,
    free_vars (mk_ipertype A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma free_vars_mk_spertype {p} :
  forall A : @NTerm p,
    free_vars (mk_spertype A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma free_vars_mk_tuni {p} :
  forall A : @NTerm p,
    free_vars (mk_tuni A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma wf_isaxiom {p} :
  forall a b c : @NTerm p,
    wf_term (mk_isaxiom a b c) <=> (wf_term a # wf_term b # wf_term c).
Proof.
  sp; split; intro k.

  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.

  - repnd.
    unfold wf_term; simpl.
    rw k0; rw k1; rw k; auto.
Qed.

Lemma nt_wf_isaxiom {p} :
  forall a b c : @NTerm p,
    nt_wf (mk_isaxiom a b c) <=> (nt_wf a # nt_wf b # nt_wf c).
Proof.
  introv.
  allrw @nt_wf_eq.
  apply wf_isaxiom.
Qed.

Lemma isprog_vars_isaxiom {p} :
  forall vs (a b c : @NTerm p),
    isprog_vars vs (mk_isaxiom a b c)
    <=>
    (isprog_vars vs a
     # isprog_vars vs b
     # isprog_vars vs c).
Proof.
  introv; split; intro k; repnd; allrw @isprog_vars_eq; allsimpl;
  allrw remove_nvars_nil_l; allrw app_nil_r;
  allrw subvars_app_l; allrw @nt_wf_isaxiom; sp.
Qed.

Lemma isprog_vars_halts {p} :
  forall vs (a : @NTerm p), isprog_vars vs (mk_halts a) <=> isprog_vars vs a.
Proof.
  introv.
  allrw @isprog_vars_eq; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw @nt_wf_eq.
  allrw <- @wf_halts_iff; sp.
Qed.

Lemma isprog_ipertype_iff {p} :
  forall a : @NTerm p, isprog a <=> isprog (mk_ipertype a).
Proof.
  introv; split; intro k.
  apply isprog_ipertype; sp.
  allrw @isprog_eq; allunfold @isprogram; allrw @nt_wf_eq.
  allrw <- @wf_ipertype_iff; sp.
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma isprog_spertype_iff {p} :
  forall a : @NTerm p, isprog a <=> isprog (mk_spertype a).
Proof.
  introv; split; intro k.
  apply isprog_spertype; sp.
  allrw @isprog_eq; allunfold @isprogram; allrw @nt_wf_eq.
  allrw <- @wf_spertype_iff; sp.
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma isprog_tuni_iff {p} :
  forall a : @NTerm p, isprog a <=> isprog (mk_tuni a).
Proof.
  introv; split; intro k.
  apply isprog_tuni; sp.
  allrw @isprog_eq; allunfold @isprogram; allrw @nt_wf_eq.
  allrw <- @wf_tuni_iff; sp.
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma wf_pair {p} :
  forall a b : @NTerm p, wf_term (mk_pair a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_spread {p} :
  forall (a : @NTerm p) v1 v2 b,
    wf_term (mk_spread a v1 v2 b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1,v2] b)); clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; sp.
  allsimpl; sp; subst; constructor; allrw @nt_wf_eq; sp.
Qed.

Lemma wf_ispair {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_ispair a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_ispair_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_ispair a b T).
Proof.
  sp; split; introv k.
  - apply wf_ispair; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.
Qed.

Lemma wf_isinl {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_isinl a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_isinl_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_isinl a b T).
Proof.
  introv; split; intro k.
  - apply wf_isinl; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.
Qed.

Lemma wf_isinr {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_isinr a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_isinr_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_isinr a b T).
Proof.
  introv; split; intro k.
  - apply wf_isinl; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.
Qed.

Lemma wf_islambda {p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_islambda a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_islambda_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_isinr a b T).
Proof.
  introv; split; intro k.
  - apply wf_islambda; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.
Qed.

Lemma wf_isaxiom_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_isinr a b T).
Proof.
  introv; split; intro k.
  - apply wf_isaxiom; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.
Qed.

Lemma wf_isint{p} :
  forall a b T : @NTerm p,
    wf_term a -> wf_term b -> wf_term T -> wf_term (mk_isint a b T).
Proof.
  intros a b T; repeat (rw <- @nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_isint_iff {p} :
  forall a b T : @NTerm p,
    (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_isint a b T).
Proof.
  introv; split; intro k.
  - apply wf_isint; sp.
  - dands; eapply oball_map_wftb_eq_otrue_implies_wf_term; try (exact k); simpl; sp.
Qed.

Lemma isprog_pi1 {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_pi1 t).
Proof.
  introv ip.
  apply isprog_spread; sp.
  apply isprog_vars_var_iff; simpl; sp.
Qed.

Lemma isprog_pi2 {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_pi2 t).
Proof.
  introv ip.
  apply isprog_spread; sp.
  apply isprog_vars_var_iff; simpl; sp.
Qed.

Lemma isprog_eta_pair {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_eta_pair t).
Proof.
  introv ip.
  unfold mk_eta_pair.
  apply isprog_pair.
  apply isprog_pi1; auto.
  apply isprog_pi2; auto.
Qed.

Definition mkc_eta_pair {p} (t : @CTerm p) :=
  let (a,p) := t in exist isprog (mk_eta_pair a) (isprog_eta_pair a p).

Lemma isprog_outl {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_outl t).
Proof.
  introv ip.
  apply isprog_decide; tcsp.
  - apply isprog_vars_mk_var; tcsp.
  - unfold isprog_vars; simpl; dands; tcsp.
Qed.

Lemma isprog_outr {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_outr t).
Proof.
  introv ip.
  apply isprog_decide; sp.
  - unfold isprog_vars; simpl; dands; tcsp.
  - apply isprog_vars_mk_var; tcsp.
Qed.

Lemma isprog_eta_inl {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_eta_inl t).
Proof.
  introv ip.
  unfold mk_eta_inl.
  apply isprog_inl.
  apply isprog_outl; auto.
Qed.

Lemma isprog_eta_inr {p} :
  forall t : @NTerm p, isprog t -> isprog (mk_eta_inr t).
Proof.
  introv ip.
  unfold mk_eta_inr.
  apply isprog_inr.
  apply isprog_outl; auto.
Qed.

Definition mkc_eta_inl {p} (t : @CTerm p) :=
  let (a,p) := t in exist isprog (mk_eta_inl a) (isprog_eta_inl a p).

Definition mkc_eta_inr {p} (t : @CTerm p) :=
  let (a,p) := t in exist isprog (mk_eta_inr a) (isprog_eta_inr a p).

Lemma fold_pi1 {p} :
  forall t : @NTerm p, mk_spread t nvarx nvary (mk_var nvarx) = mk_pi1 t.
Proof. sp. Qed.

Lemma fold_pi2 {p} :
  forall t : @NTerm p, mk_spread t nvarx nvary (mk_var nvary) = mk_pi2 t.
Proof. sp. Qed.

Lemma fold_eta_pair {p} :
  forall t : @NTerm p, mk_pair (mk_pi1 t) (mk_pi2 t) = mk_eta_pair t.
Proof. sp. Qed.

Lemma wf_pi1 {p} :
  forall t : @NTerm p, wf_term (mk_pi1 t) <=> wf_term t.
Proof.
  introv.
  rw @wf_spread; split; sp.
Qed.

Lemma wf_pi2 {p} :
  forall t : @NTerm p, wf_term (mk_pi2 t) <=> wf_term t.
Proof.
  introv.
  rw @wf_spread; split; sp.
Qed.

Lemma wf_eta_pair {p} :
  forall t : @NTerm p, wf_term (mk_eta_pair t) <=> wf_term t.
Proof.
  introv.
  unfold mk_eta_pair.
  rw @wf_pair.
  rw @wf_pi1.
  rw @wf_pi2.
  split; sp.
Qed.

Lemma isprogram_spread_iff {p} :
  forall (a : @NTerm p) v1 v2 b,
    (isprogram a
     # subvars (free_vars b) [v1,v2]
     # nt_wf b)
    <=> isprogram (mk_spread a v1 v2 b).
Proof.
  introv; split; intro isp; repnd.
  apply isprogram_spread; auto.
  inversion isp as [cl wf].
  inversion wf as [| o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1,v2] b)); clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  unfold closed in cl; simpl in cl; rw remove_nvars_nil_l in cl; rw app_nil_r in cl.
  apply app_eq_nil in cl; repnd.
  allfold (closed a).
  dands; auto.
  constructor; sp.
  rw subvars_prop; introv i.
  rw nil_remove_nvars_iff in cl.
  apply cl in i; sp.
Qed.

Lemma isprogram_spread_iff2 {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprogram (mk_spread a v1 v2 b)
    <=> isprogram a # isprogram_bt (bterm [v1, v2] b).
Proof.
  introv.
  rw <- @isprogram_spread_iff.
  unfold isprogram_bt; simpl.
  unfold closed_bt; simpl.
  rw <- null_iff_nil.
  rw null_remove_nvars.
  rw subvars_prop.
  split; intro k; repnd; dands; auto.
  inversion k; sp.
Qed.

Lemma isprogram_dsup_iff {p} :
  forall (a : @NTerm p) v1 v2 b,
    (isprogram a
     # subvars (free_vars b) [v1,v2]
     # nt_wf b)
    <=> isprogram (mk_dsup a v1 v2 b).
Proof.
  introv; split; intro isp; repnd.
  apply isprogram_dsup; auto.
  inversion isp as [cl wf].
  inversion wf as [| o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1,v2] b)); clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  unfold closed in cl; simpl in cl; rw remove_nvars_nil_l in cl; rw app_nil_r in cl.
  apply app_eq_nil in cl; repnd.
  allfold (closed a).
  dands; auto.
  constructor; sp.
  rw subvars_prop; introv i.
  rw nil_remove_nvars_iff in cl.
  apply cl in i; sp.
Qed.

Lemma isprogram_dsup_iff2 {p} :
  forall (a : @NTerm p) v1 v2 b,
    isprogram (mk_dsup a v1 v2 b)
    <=> isprogram a # isprogram_bt (bterm [v1, v2] b).
Proof.
  introv.
  rw <- @isprogram_dsup_iff.
  unfold isprogram_bt; simpl.
  unfold closed_bt; simpl.
  rw <- null_iff_nil.
  rw null_remove_nvars.
  rw subvars_prop.
  split; intro k; repnd; dands; auto.
  inversion k; sp.
Qed.

Lemma isprogram_decide_iff {p} :
  forall (a : @NTerm p) v1 b1 v2 b2,
    (isprogram a
     # subvars (free_vars b1) [v1]
     # subvars (free_vars b2) [v2]
     # nt_wf b1
     # nt_wf b2)
    <=> isprogram (mk_decide a v1 b1 v2 b2).
Proof.
  introv; split; intro isp; repnd.
  apply isprogram_decide; auto.
  inversion isp as [cl wf].
  inversion wf as [| o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1] b1)) (bwf (bterm [v2] b2)); clear bwf; intros bwf1 bwf2 bwf3.
  autodimp bwf1 hyp; autodimp bwf2 hyp; autodimp bwf3 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  inversion bwf3; subst.
  unfold closed in cl; simpl in cl; rw remove_nvars_nil_l in cl; rw app_nil_r in cl.
  apply app_eq_nil in cl; repnd.
  allfold (closed a).
  apply app_eq_nil_iff in cl; repnd.
  rw nil_remove_nvars_iff in cl1.
  rw nil_remove_nvars_iff in cl.
  dands; auto.
  constructor; sp.
  rw subvars_prop; sp.
  rw subvars_prop; sp.
Qed.

Lemma isprogram_decide_iff2 {p} :
  forall (a : @NTerm p) v1 b1 v2 b2,
    isprogram (mk_decide a v1 b1 v2 b2)
    <=> isprogram a # isprogram_bt (bterm [v1] b1) # isprogram_bt (bterm [v2] b2).
Proof.
  introv.
  rw <- @isprogram_decide_iff.
  unfold isprogram_bt; simpl.
  unfold closed_bt; simpl.
  repeat (rw <- null_iff_nil).
  repeat (rw null_remove_nvars).
  repeat (rw subvars_prop).
  split; intro k; repnd; dands; auto.
  inversion k1; sp.
  inversion k; sp.
Qed.

Lemma isprogram_outl {p} :
  forall t : @NTerm p, isprogram (mk_outl t) <=> isprogram t.
Proof.
  introv.
  rw <- @isprogram_decide_iff; simpl; split; intro i; repnd; auto.
  dands; auto.
  pose proof (@isprogram_bot p) as X.
  destruct X. auto. 
Qed.

Lemma isprogram_outr {p} :
  forall t : @NTerm p, isprogram (mk_outr t) <=> isprogram t.
Proof.
   introv.
  rw <- @isprogram_decide_iff; simpl; split; intro i; repnd; auto.
  dands; auto.
  pose proof (@isprogram_bot p) as X.
  destruct X. auto. 
Qed.


Lemma isprogram_pi1 {p} :
  forall t : @NTerm p, isprogram (mk_pi1 t) <=> isprogram t.
Proof.
  introv.
  rw <- @isprogram_spread_iff; simpl; split; intro i; repnd; auto.
  dands; auto.
  rw subvars_cons_l; sp.
Qed.

Lemma isprogram_pi2 {p} :
  forall t : @NTerm p, isprogram (mk_pi2 t) <=> isprogram t.
Proof.
  introv.
  rw <- @isprogram_spread_iff; simpl; split; intro i; repnd; auto.
  dands; auto.
  rw subvars_cons_l; sp.
Qed.

Lemma isprogram_eta_pair {p} :
  forall t : @NTerm p, isprogram (mk_eta_pair t) <=> isprogram t.
Proof.
  introv.
  rw <- @isprogram_pair_iff.
  rw @isprogram_pi1.
  rw @isprogram_pi2.
  split; sp.
Qed.

Lemma iscvalue_mkc_tequality {p} :
  forall t1 t2 : @CTerm p, iscvalue (mkc_tequality t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_tequality; allrw @isprog_eq; auto.
  apply isprogram_tequality; sp.
Qed.

Lemma isprog_pw_iff {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C q,
    isprog (mk_pw P ap A bp ba B cp ca cb C q)
           <=> (isprog P
                # isprog_vars [ap] A
                # isprog_vars [bp, ba] B
                # isprog_vars [cp, ca, cb] C
                # isprog q).
Proof.
  introv; split; intro isp.

  rw @isprog_eq in isp.
  inversion isp as [ cl wf ].
  inversion wf as [| o lnt j e ]; subst.
  generalize (j (nobnd P))
             (j (bterm [ap] A))
             (j (bterm [bp,ba] B))
             (j (bterm [cp,ca,cb] C))
             (j (nobnd q)); clear j;
    intros i1 i2 i3 i4 i5; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  repeat (dest_imp i3 hyp).
  repeat (dest_imp i4 hyp).
  repeat (dest_imp i5 hyp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst.
  unfold closed in cl; simpl in cl; allrw remove_nvars_nil_l; allrw app_nil_r.
  rw <- null_iff_nil in cl.
  allrw null_app; repnd.
  allrw null_remove_nvars_subvars.
  allrw null_iff_nil.
  dands.
  rw @isprog_eq; constructor; sp.
  rw @isprog_vars_eq; sp.
  rw @isprog_vars_eq; sp.
  rw @isprog_vars_eq; sp.
  rw @isprog_eq; constructor; sp.

  apply isprog_pw; sp.
Qed.

Lemma isprog_pm_iff {p} :
  forall (P : @NTerm p) ap A bp ba B cp ca cb C q,
    isprog (mk_pm P ap A bp ba B cp ca cb C q)
           <=> (isprog P
                # isprog_vars [ap] A
                # isprog_vars [bp, ba] B
                # isprog_vars [cp, ca, cb] C
                # isprog q).
Proof.
  introv; split; intro isp.

  rw @isprog_eq in isp.
  inversion isp as [ cl wf ].
  inversion wf as [| o lnt j e ]; subst.
  generalize (j (nobnd P))
             (j (bterm [ap] A))
             (j (bterm [bp,ba] B))
             (j (bterm [cp,ca,cb] C))
             (j (nobnd q)); clear j;
    intros i1 i2 i3 i4 i5; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  repeat (dest_imp i3 hyp).
  repeat (dest_imp i4 hyp).
  repeat (dest_imp i5 hyp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst.
  unfold closed in cl; simpl in cl; allrw remove_nvars_nil_l; allrw app_nil_r.
  rw <- null_iff_nil in cl.
  allrw null_app; repnd.
  allrw null_remove_nvars_subvars.
  allrw null_iff_nil.
  dands.
  rw @isprog_eq; constructor; sp.
  rw @isprog_vars_eq; sp.
  rw @isprog_vars_eq; sp.
  rw @isprog_vars_eq; sp.
  rw @isprog_eq; constructor; sp.

  apply isprog_pm; sp.
Qed.

Lemma isprogram_exception_implies {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm Exc bterms)
    -> {a : NTerm
        $ {t : NTerm
        $ bterms = [bterm [] a, bterm [] t]
        # isprogram a
        # isprogram t}}.
Proof.
  introv isp.
  inversion isp as [c w].
  inversion w as [|o lnt bw m]; subst; allsimpl.
  repeat (destruct bterms; ginv).
  allsimpl; ginv.
  destruct b as [l1 t1]; destruct b0 as [l2 t2].
  destruct l1; destruct l2; ginv.
  allunfold @num_bvars; allsimpl; GC.
  unfold closed in c; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw app_eq_nil_iff.
  pose proof (bw (bterm [] t1)) as w1.
  pose proof (bw (bterm [] t2)) as w2.
  repeat (autodimp w1 hyp); repeat (autodimp w2 hyp).
  inversion w1; inversion w2; subst.
  exists t1 t2; dands; auto; constructor; sp.
Qed.

Lemma iscan_implies {p} :
  forall t : @NTerm p,
    iscan t
    -> {c : CanonicalOp
        & {bterms : list BTerm
        & t = oterm (Can c) bterms}}.
Proof.
  introv isc.
  destruct t as [v|op bs]; try (complete (inversion isc)).
  - destruct op; try (complete (inversion isc)).
    exists c bs; sp.
Qed.

Lemma isexc_implies {p} :
  forall t : @NTerm p,
    isexc t
    -> isprogram t
    -> {a : NTerm & {e : NTerm & t = mk_exception a e}}.
Proof.
  introv isc isp.
  destruct t; try (complete (inversion isc)).
  destruct o; try (complete (inversion isc)).
  apply isprogram_exception_implies in isp; sp; subst.
  eexists; eexists; reflexivity.
Qed.

Lemma isexc_implies2 {p} :
  forall t : @NTerm p,
    isexc t
    -> {l : list BTerm & t = oterm Exc l}.
Proof.
  introv isc.
  destruct t; try (complete (inversion isc)).
  destruct o; try (complete (inversion isc)).
  eexists; eexists; sp.
Qed.

Lemma isprogram_trycatch_implies {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NTryCatch) bterms)
    -> {t : NTerm
        $ {a : NTerm
        $ {v : NVar
        $ {b : NTerm
           $ bterms = [bterm [] t, bterm [] a, bterm [v] b]
           # isprogram t
           # isprogram a
           # isprogram_bt (bterm [v] b)}}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b as [l1 t1]; allsimpl; cpx.
  destruct b0 as [l2 t2]; allsimpl; cpx.
  destruct b1 as [l3 t3]; allsimpl; cpx.
  destruct l1; allsimpl; cpx.
  destruct l2; allsimpl; cpx.
  repeat (destruct l3; allsimpl; cpx).
  generalize (isp (bterm [] t1)) (isp (bterm [] t2)) (isp (bterm [n] t3)); intros isp1 isp2 isp3.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  repeat (autodimp isp3 hyp).
  apply isprogram_bt_nobnd in isp1.
  apply isprogram_bt_nobnd in isp2.
  exists t1 t2 n t3; sp.
Qed.

Lemma isprogram_fresh_implies {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NFresh) bterms)
    -> {v : NVar
        $ {b : NTerm
           $ bterms = [bterm [v] b]
           # isprogram_bt (bterm [v] b)}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [n0] n)); intros isp1.
  repeat (autodimp isp1 hyp).
  exists n0 n; sp.
Qed.

Lemma isprogram_cbv_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NCbv) bterms)
    -> {t : NTerm
        $ {v : NVar
        $ {b : NTerm
           $ bterms = [bterm [] t, bterm [v] b]
           # isprogram t
           # isprogram_bt (bterm [v] b)}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [n1] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n n1 n0; sp.
Qed.

Lemma isprogram_apply_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NApply) bterms)
    -> {f : NTerm
        $ {a : NTerm
           $ bterms = [bterm [] f, bterm [] a]
           # isprogram f
           # isprogram a}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  apply isprogram_bt_nobnd in isp2.
  exists n n0; sp.
Qed.

Lemma isprogram_eapply_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NEApply) bterms)
    -> {f : NTerm
        $ {a : NTerm
           $ bterms = [bterm [] f, bterm [] a]
           # isprogram f
           # isprogram a}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  apply isprogram_bt_nobnd in isp2.
  exists n n0; sp.
Qed.

(*
Lemma isprogram_apseq_implies {p} :
  forall f (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NApseq f)) bterms)
    -> {a : NTerm
        $ bterms = [bterm [] a]
        # isprogram a}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)); intros isp1.
  repeat (autodimp isp1 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n; sp.
Qed.
 *)

Lemma isprogram_parallel_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NParallel) bterms)
    -> {a : NTerm
        $ {b : NTerm
        $ bterms = [bterm [] a, bterm [] b]
        # isprogram a
        # isprogram b}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  apply isprogram_bt_nobnd in isp2.
  exists n n0; sp.
Qed.

Lemma isprogram_fix_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NFix) bterms)
    -> {f : NTerm
        $ bterms = [bterm [] f]
        # isprogram f}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  generalize (isp (bterm [] n)); intros isp1.
  repeat (autodimp isp1 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n; sp.
Qed.

Lemma isprogram_sleep_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NSleep) bterms)
    -> {t : NTerm
        $ bterms = [bterm [] t]
        # isprogram t}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  generalize (isp (bterm [] n)); intros isp1.
  repeat (autodimp isp1 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n; sp.
Qed.

Lemma isprogram_tuni_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NTUni) bterms)
    -> {t : NTerm
        $ bterms = [bterm [] t]
        # isprogram t}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  generalize (isp (bterm [] n)); intros isp1.
  repeat (autodimp isp1 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n; sp.
Qed.

Lemma isprogram_minus_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NMinus) bterms)
    -> {t : NTerm
        $ bterms = [bterm [] t]
        # isprogram t}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  generalize (isp (bterm [] n)); intros isp1.
  repeat (autodimp isp1 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n; sp.
Qed.

Lemma isprogram_spread_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NSpread) bterms)
    -> {t : NTerm
        $ {v1 : NVar
        $ {v2 : NVar
        $ {b : NTerm
           $ bterms = [bterm [] t, bterm [v1,v2] b]
           # isprogram t
           # isprogram_bt (bterm [v1,v2] b)}}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [n1,n2] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n n1 n2 n0; sp.
Qed.

Lemma isprogram_dsup_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NDsup) bterms)
    -> {t : NTerm
        $ {v1 : NVar
        $ {v2 : NVar
        $ {b : NTerm
           $ bterms = [bterm [] t, bterm [v1,v2] b]
           # isprogram t
           # isprogram_bt (bterm [v1,v2] b)}}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [n1,n2] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n n1 n2 n0; sp.
Qed.

Lemma isprogram_decide_implies {p} :
  forall bterms : list (@BTerm p),
    isprogram (oterm (NCan NDecide) bterms)
    -> {t : NTerm
        $ {v1 : NVar
        $ {b1 : NTerm
        $ {v2 : NVar
        $ {b2 : NTerm
           $ bterms = [bterm [] t, bterm [v1] b1, bterm [v2] b2]
           # isprogram t
           # isprogram_bt (bterm [v1] b1)
           # isprogram_bt (bterm [v2] b2)}}}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  destruct b1; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [n1] n0)) (isp (bterm [n3] n2));
    intros isp1 isp2 isp3.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  repeat (autodimp isp3 hyp).
  apply isprogram_bt_nobnd in isp1.
  exists n n1 n0 n3 n2; sp.
Qed.

Lemma isprogram_arithop_implies {p} :
  forall o (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NArithOp o)) bterms)
    -> {a : NTerm
        $ {b : NTerm
           $ bterms = [bterm [] a, bterm [] b]
           # isprogram a
           # isprogram b}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [] n0)); intros isp1 isp2.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  apply isprogram_bt_nobnd in isp1.
  apply isprogram_bt_nobnd in isp2.
  exists n n0; sp.
Qed.

Lemma isprogram_arithop_iff {p} :
  forall o (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NArithOp o)) bterms)
    <=> {a : NTerm
        $ {b : NTerm
           $ bterms = [bterm [] a, bterm [] b]
           # isprogram a
           # isprogram b}}.
Proof.
  introv; split; intro k.
  apply isprogram_arithop_implies in k; auto.
  exrepnd; subst.
  apply isprogram_ot_iff; simpl.
  unfold num_bvars; simpl; dands; sp; subst;
  apply implies_isprogram_bt0; auto.
Qed.

Lemma isprogram_compop_implies {p} :
  forall o (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NCompOp o)) bterms)
    -> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
        $ {d : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c, bterm [] d]
           # isprogram a
           # isprogram b
           # isprogram c
           # isprogram d}}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  destruct b1; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct l0; allsimpl; cpx.
  destruct b2; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  generalize
    (isp (bterm [] n))
    (isp (bterm [] n0))
    (isp (bterm [] n1))
    (isp (bterm [] n2));
    intros isp1 isp2 isp3 isp4.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  repeat (autodimp isp3 hyp).
  repeat (autodimp isp4 hyp).
  allapply @isprogram_bt_nobnd.
  exists n n0 n1 n2; sp.
Qed.

Lemma isprogram_compop_iff {p} :
  forall o (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NCompOp o)) bterms)
    <=> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
        $ {d : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c, bterm [] d]
           # isprogram a
           # isprogram b
           # isprogram c
           # isprogram d}}}}.
Proof.
  introv; split; intro k.
  apply isprogram_compop_implies in k; auto.
  exrepnd; subst.
  apply isprogram_ot_iff; unfold num_bvars; simpl; sp; subst;
  apply implies_isprogram_bt0; auto.
Qed.

Lemma isprogram_cantest_implies {p} :
  forall o (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NCanTest o)) bterms)
    -> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c]
           # isprogram a
           # isprogram b
           # isprogram c}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  destruct b1; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct l0; allsimpl; cpx.
  generalize
    (isp (bterm [] n))
    (isp (bterm [] n0))
    (isp (bterm [] n1));
    intros isp1 isp2 isp3.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  repeat (autodimp isp3 hyp).
  allapply @isprogram_bt_nobnd.
  exists n n0 n1; sp.
Qed.

Lemma isprogram_cantest_iff {p} :
  forall o (bterms : list (@BTerm p)),
    isprogram (oterm (NCan (NCanTest o)) bterms)
    <=> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c]
           # isprogram a
           # isprogram b
           # isprogram c}}}.
Proof.
  introv; split; intro k.
  apply isprogram_cantest_implies in k; auto.
  exrepnd; subst.
  apply isprogram_ot_iff; unfold num_bvars; simpl; sp; subst;
  apply implies_isprogram_bt0; auto.
Qed.


Lemma isprog_vars_btrue {o} :
  forall vs, @isprog_vars o vs mk_btrue.
Proof.
  introv.
  rw @isprog_vars_eq; simpl; dands; auto.
  constructor; simpl; tcsp.
  introv i; repndors; subst; tcsp.
  constructor; eauto with slow.
Qed.

Lemma isprog_vars_bfalse {o} :
  forall vs, @isprog_vars o vs mk_bfalse.
Proof.
  introv.
  rw @isprog_vars_eq; simpl; dands; auto.
  constructor; simpl; tcsp.
  introv i; repndors; subst; tcsp.
  constructor; eauto with slow.
Qed.

Lemma isprog_vars_le_implies {o} :
  forall (a b : @NTerm o) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_le a b).
Proof.
  introv u v.
  apply isprog_vars_le; sp.
Qed.

Lemma isprog_vars_less_than {o} :
  forall (a b : @NTerm o) vs,
    isprog_vars vs (mk_less_than a b) <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv; unfold mk_less_than.
  rw @isprog_vars_less; split; sp.
  apply isprog_vars_true_iff; sp.
Qed.

Lemma isprog_implies_isprog_vars_nil {o} :
  forall t,  @isprog o t -> isprog_vars [] t.
Proof.
  introv isp.
  apply isprog_eq in isp.
  apply isprog_vars_eq.
  rw subvars_nil_r; auto.
Qed.

Lemma isprog_vars_nil_implies_isprog {o} :
  forall t, isprog_vars [] t -> @isprog o t.
Proof.
  introv isp.
  apply isprog_eq.
  apply isprog_vars_eq in isp; repnd.
  apply subvars_nil_r in isp0.
  unfold isprogram; auto.
Qed.

Lemma isprog_vars_nil_iff_isprog {o} :
  forall t, @isprog o t <=> isprog_vars [] t.
Proof.
  introv; split; intro k.
  apply isprog_implies_isprog_vars_nil; auto.
  apply isprog_vars_nil_implies_isprog; auto.
Qed.

Lemma isprog_less_than {o} :
  forall a b : @NTerm o,
    isprog (mk_less_than a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_less_than.
Qed.

Lemma isprog_less_than_implies {o} :
  forall a b : @NTerm o,
    isprog a
    -> isprog b
    -> isprog (mk_less_than a b).
Proof.
  introv x y.
  apply isprog_less_than; sp.
Qed.

Lemma isprog_vars_prod_implies {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_prod a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_prod; sp.
Qed.

Lemma isprog_vars_less_than_implies {o} :
  forall (a b : @NTerm o) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_less_than a b).
Proof.
  introv u v.
  apply isprog_vars_less_than; sp.
Qed.

Lemma isprog_ot_iff {p} :
  forall (o : @Opid p) (bts : list BTerm),
    isprog (oterm o bts)
    <=>
    map num_bvars bts = OpBindings o
    # (forall bt : BTerm, LIn bt bts -> isprog_bt bt).
Proof.
  introv.
  rw @isprog_eq.
  rw @isprogram_ot_iff; split; intro k; repnd; dands; auto;
  introv i; apply isprogram_bt_eq; auto.
Qed.

Lemma isprog_decide_iff {o} :
  forall (a : @NTerm o) (v1 : NVar) (a1 : NTerm) (v2 : NVar) (a2 : NTerm),
    isprog (mk_decide a v1 a1 v2 a2)
           <=> (isprog a # isprog_vars [v1] a1 # isprog_vars [v2] a2).
Proof.
  introv.
  split; intro k; repnd; try (apply isprog_decide; auto).
  unfold mk_decide in k.
  rw @isprog_ot_iff in k; repnd; allsimpl; clear k0.
  pose proof (k (nobnd a)) as h1; autodimp h1 hyp.
  pose proof (k (bterm [v1] a1)) as h2; autodimp h2 hyp.
  pose proof (k (bterm [v2] a2)) as h3; autodimp h3 hyp.
Qed.

Lemma isprog_vars_not {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs (mk_not t) <=> isprog_vars vs t.
Proof.
  introv.
  unfold mk_not.
  rw <- @isprog_vars_fun.
  rw @isprog_vars_void_iff.
  split; sp.
Qed.

Lemma implies_isprog_vars_not {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t -> isprog_vars vs (mk_not t).
Proof.
  introv isp.
  apply isprog_vars_not; auto.
Qed.

Lemma isprog_vars_disjoint_implies_isprog {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t
    -> disjoint vs (free_vars t)
    -> isprog t.
Proof.
  introv isp disj.
  allrw @isprog_vars_eq; repnd.
  rw @isprog_eq.
  constructor; auto.
  unfold closed.
  apply null_iff_nil.
  introv i.
  rw subvars_prop in isp0.
  applydup isp0 in i.
  apply disj in i0; sp.
Qed.

(* end hide *)

(**

  We say that a term [t] is covered by a list of variables [vs] if the
  free variables of [t] are all in [vs].

*)

Definition covered {p} (t : @NTerm p) (vs : list NVar) :=
  subvars (free_vars t) vs.

(* begin hide *)

Lemma covered_proof_irrelevance {p} :
  forall t vs,
  forall x y : @covered p t vs,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : covered ?t ?vs , H2 : covered ?t ?vs |- _ ] =>
    pose proof (covered_proof_irrelevance t vs H2 H1) as h; subst
end : pi.

Lemma isprog_vars_implies_covered {o} :
  forall (t : @NTerm o) vs,
    isprog_vars vs t -> covered t vs.
Proof.
  introv isp.
  unfold covered.
  allrw @isprog_vars_eq; sp.
Qed.
Hint Resolve isprog_vars_implies_covered : slow.


(* --- isprog hints --- *)
Hint Resolve isprog_lam : isprog.
Hint Resolve isprog_vars_lam : isprog.
Hint Resolve isprog_vars_isect : isprog.
Hint Resolve isprog_vars_base : isprog.
Hint Resolve isprog_vars_equality : isprog.
Hint Resolve isprog_vars_var_if : isprog.
Hint Resolve isprog_vars_if_isprog : isprog.
Hint Extern 100 (LIn _ _) => complete (simpl; sp) : isprog.
Hint Resolve isprog_implies : isprog.

Hint Resolve isprog_vars_btrue : slow.
Hint Resolve isprog_vars_bfalse : slow.
Hint Resolve isprog_vars_le_implies : slow.
Hint Resolve isprog_vars_less_than_implies : slow.
Hint Resolve isprog_vars_prod_implies : slow.

Hint Resolve wf_function : slow.
Hint Resolve wf_product : slow.

Lemma ispexc_exception {p} :
  forall a e : @NTerm p,
    isprogram a -> isprogram e -> ispexc (mk_exception a e).
Proof.
  introv isp1 isp2.
  split.
  constructor.
  apply isprogram_exception; auto.
Qed.
Hint Resolve ispexc_exception.

Lemma isp_can_or_exc_exception {p} :
  forall a e : @NTerm p,
    isprogram a
    -> isprogram e
    -> isp_can_or_exc (mk_exception a e).
Proof.
  introv isp1 isp2.
  split; auto.
  apply isprogram_exception; auto.
  right; sp.
Qed.
Hint Resolve isp_can_or_exc_exception.

Lemma free_vars_list_nil {p} :
  forall ts : list (@NTerm p),
    (forall t, LIn t ts -> isprog t)
    -> free_vars_list ts = [].
Proof.
  induction ts; introv h; allsimpl; auto.
  allrw IHts; sp.
  pose proof (h a) as k; autodimp k hyp.
  apply isprog_eq in k.
  inversion k.
  allunfold @closed.
  allrw; sp.
Qed.

Lemma newvarlst_prog {p} :
  forall ts : list (@NTerm p),
    (forall t, LIn t ts -> isprog t)
    -> newvarlst ts = nvarx.
Proof.
  introv h.
  unfold newvarlst.
  rw @free_vars_list_nil; auto.
Qed.

Lemma nt_wf_oterm_iff {p} :
  forall o (bts : list (@BTerm p)),
    nt_wf (oterm o bts)
          <=> map num_bvars bts = OpBindings o
              # forall b, LIn b bts -> bt_wf b.
Proof.
  introv. sp_iff Case; introv h; repnd.
  - Case "->".
    inverts h as Hbf Hmap. split; auto.
  - Case "<-".
    constructor; auto.
Qed.

Lemma isprog_vars_ot_iff {p} :
  forall (vs : list NVar) (o : @Opid p) (bts : list BTerm),
    isprog_vars vs (oterm o bts)
    <=>
    map num_bvars bts = OpBindings o
    # (forall l t, LIn (bterm l t) bts -> isprog_vars (vs ++ l) t).
Proof.
  introv.
  rw @isprog_vars_eq; simpl.
  rw @nt_wf_oterm_iff.
  rw subvars_flat_map.
  split; intro k; repnd; dands; auto; introv i.
  - apply isprog_vars_eq; dands.
    apply k0 in i; simpl in i.
    rw subvars_remove_nvars in i; auto.
    apply k in i; inversion i; subst; auto.
  - destruct x; simpl.
    rw subvars_remove_nvars.
    apply k in i.
    apply isprog_vars_eq in i; repnd; auto.
  - destruct b.
    apply k in i.
    apply isprog_vars_eq in i; repnd; auto.
Qed.

Lemma nt_wf_bottom {o} : nt_wf (@mk_bottom o).
Proof.
  repeat constructor; simpl; introv i; dorn i; cpx; subst.
  repeat constructor; simpl; introv i; dorn i; cpx; subst.
  repeat constructor; simpl; introv i; dorn i; cpx; subst.
Qed.

Lemma closed_if_program {o} :
  forall t : @NTerm o, isprogram t -> closed t.
Proof.
  introv isp; destruct isp; auto.
Qed.
Hint Resolve closed_if_program : slow.

Definition mk_compop {p} x (a b c d : @NTerm p) :=
  oterm (NCan (NCompOp x)) [nobnd a, nobnd b, nobnd c, nobnd d].

Lemma wf_compop {p} :
  forall x (a b c d : @NTerm p),
    wf_term a -> wf_term b -> wf_term c -> wf_term d
    -> wf_term (mk_compop x a b c d).
Proof.
  introv wa wb wc wd; allrw <- @nt_wf_eq.
  constructor; simpl; tcsp.
  introv k; repndors; subst; tcsp; constructor; auto.
Qed.

Lemma wf_compop_iff {p} :
  forall x (a b c d : @NTerm p),
    wf_term (mk_compop x a b c d) <=> (wf_term a # wf_term b # wf_term c # wf_term d).
Proof.
  introv; split; intro k.
  - allrw @wf_term_eq.
    inversion k as [|? ? i e]; subst; allsimpl.
    pose proof (i (nobnd a)) as ha.
    pose proof (i (nobnd b)) as hb.
    pose proof (i (nobnd c)) as hc.
    pose proof (i (nobnd d)) as hd.
    repeat (autodimp ha hyp).
    repeat (autodimp hb hyp).
    repeat (autodimp hc hyp).
    repeat (autodimp hd hyp).
    inversion ha; subst.
    inversion hb; subst.
    inversion hc; subst.
    inversion hd; subst; sp.
  - apply wf_compop; sp.
Qed.

Definition mk_arithop {p} x (a b : @NTerm p) :=
  oterm (NCan (NArithOp x)) [nobnd a, nobnd b].

Lemma wf_arithop {p} :
  forall x (a b : @NTerm p),
    wf_term a -> wf_term b
    -> wf_term (mk_arithop x a b).
Proof.
  introv wa wb; allrw <- @nt_wf_eq.
  constructor; simpl; tcsp.
  introv k; repndors; subst; tcsp; constructor; auto.
Qed.

Lemma wf_arithop_iff {p} :
  forall x (a b : @NTerm p),
    wf_term (mk_arithop x a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro k.
  - allrw @wf_term_eq.
    inversion k as [|? ? i e]; subst; allsimpl.
    pose proof (i (nobnd a)) as ha.
    pose proof (i (nobnd b)) as hb.
    repeat (autodimp ha hyp).
    repeat (autodimp hb hyp).
    inversion ha; subst.
    inversion hb; subst; sp.
  - apply wf_arithop; sp.
Qed.

Lemma isprog_arithop {p} :
  forall (op: ArithOp) (a b : @NTerm p), isprog a -> isprog b -> isprog (mk_arithop op a b).
Proof.
  sp; allrw @isprog_eq; intros; apply isprogram_arithop_iff; sp.
  exists a b; auto.
Qed.

Definition mkc_arithop {p} (op: ArithOp) (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_arithop op a b) (isprog_arithop op a b x y).

Lemma wf_can_test {p} :
  forall x (a b c : @NTerm p),
    wf_term a -> wf_term b -> wf_term c
    -> wf_term (mk_can_test x a b c).
Proof.
  introv wa wb wc; allrw <- @nt_wf_eq.
  constructor; simpl; tcsp.
  introv k; repndors; subst; tcsp; constructor; auto.
Qed.

Lemma wf_can_test_iff {p} :
  forall x (a b c : @NTerm p),
    wf_term (mk_can_test x a b c) <=> (wf_term a # wf_term b # wf_term c).
Proof.
  introv; split; intro k.
  - allrw @wf_term_eq.
    inversion k as [|? ? i e]; subst; allsimpl.
    pose proof (i (nobnd a)) as ha.
    pose proof (i (nobnd b)) as hb.
    pose proof (i (nobnd c)) as hc.
    repeat (autodimp ha hyp).
    repeat (autodimp hb hyp).
    repeat (autodimp hc hyp).
    inversion ha; subst.
    inversion hb; subst.
    inversion hc; subst; sp.
  - apply wf_can_test; sp.
Qed.

Lemma wf_dsup {p} :
  forall (a : @NTerm p) v1 v2 b,
    wf_term (mk_dsup a v1 v2 b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1,v2] b)); clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; sp.
  allsimpl; sp; subst; constructor; allrw @nt_wf_eq; sp.
Qed.

Lemma wf_sup_iff {p} :
  forall a b : @NTerm p, wf_term (mk_sup a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_refl_iff {p} :
  forall a : @NTerm p, wf_term (mk_refl a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_inl {p} :
  forall a : @NTerm p, wf_term (mk_inl a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_inr {p} :
  forall a : @NTerm p, wf_term (mk_inr a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma wf_decide {p} :
  forall (a : @NTerm p) v1 b1 v2 b2,
    wf_term (mk_decide a v1 b1 v2 b2) <=> (wf_term a # wf_term b1 # wf_term b2).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1] b1)) (bwf (bterm [v2] b2));
    clear bwf; intros bwf1 bwf2 bwf3.
  autodimp bwf1 hyp; autodimp bwf2 hyp; autodimp bwf3 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  inversion bwf3; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; sp.
  allsimpl; sp; subst; constructor; allrw @nt_wf_eq; sp.
Qed.

Lemma wf_fix_iff {p} :
  forall t : @NTerm p,
    wf_term (mk_fix t) <=> wf_term t.
Proof.
  introv; split; intro k.
  - allrw @wf_term_eq.
    inversion k as [|? ? i]; allsimpl; subst; ginv.
    pose proof (i (bterm [] t)) as h; autodimp h hyp.
    inversion h; subst; auto.
  - apply wf_fix; auto.
Qed.

Lemma closed_bt_bterm {o} :
  forall vs (t : @NTerm o),
    closed_bt (bterm vs t)
    <=> subvars (free_vars t) vs.
Proof.
  introv.
  unfold closed_bt; simpl.
  rw nil_remove_nvars_iff.
  rw subvars_prop; sp.
Qed.

Lemma wf_fresh {p} :
  forall v (b : @NTerm p), wf_term b -> wf_term (mk_fresh v b).
Proof.
  intros v b; repeat (rw <- @nt_wf_eq).
  intros ntb; inversion ntb; subst; constructor; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma wf_fresh_iff {p} :
  forall v (b : @NTerm p), wf_term (mk_fresh v b) <=> wf_term b.
Proof.
  introv; split; intro i; try (apply wf_fresh; sp).
  allrw @wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (bterm [v] b)); intros j.
  dest_imp j hyp; sp.
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_subvars {o} :
  forall (t : @NTerm o) vs1 vs2,
    subvars vs1 vs2
    -> isprog_vars vs1 t
    -> isprog_vars vs2 t.
Proof.
  introv sv isp.
  allrw @isprog_vars_eq; repnd; dands; auto.
  eapply subvars_trans; eauto.
Qed.
Hint Resolve isprog_vars_subvars : slow.

Lemma nt_wf_eapply_iff {p} :
  forall (bs : list (@BTerm p)),
    nt_wf (oterm (NCan NEApply) bs)
    <=> {a : NTerm
        $ {b : NTerm
        $ bs = [bterm [] a, bterm [] b]
        # nt_wf a
        # nt_wf b}}.
Proof.
  introv; split; intro k.
  - inversion k as [|? ? imp e]; clear k; subst.
    allsimpl.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    destruct l2; ginv.
    pose proof (imp (bterm [] t1)) as h1.
    autodimp h1 hyp.
    pose proof (imp (bterm [] t2)) as h2.
    autodimp h2 hyp.
    allrw @bt_wf_iff.
    exists t1 t2; dands; auto.
  - exrepnd; subst.
    repeat constructor.
    introv i; allsimpl; repndors; subst; tcsp.
Qed.

(* end hide *)
