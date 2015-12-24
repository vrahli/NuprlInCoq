(*

  Copyright 2014 Cornell University

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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export arith_props.
Require Import continuity.
Require Import continuity2_2.
Require Import continuity3_2_v2.
Require Export continuity_defs2.
Require Export continuity_defs_ceq.

Lemma comp_force_int_app_F_c {o} :
  forall lib (F f : @CTerm o) x z,
    reduces_toc
      lib
      (force_int_F_c x F f)
      (mkc_integer z)
    -> {b : nat
        & forall (e : CTerm) b',
            b <= b'
            -> reduces_toc
                 lib
                 (force_int_bound_F_c x b' F f e)
                 (mkc_integer z)}.
Proof.
  introv r.
  unfold reduces_toc in r.
  rw @get_cterm_force_int_F_c in r.
  simpl in r.
  apply comp_force_int_app_F in r; exrepnd; eauto with slow.
  exists b.
  introv l.
  pose proof (r0 (get_cterm e) b') as h.
  repeat (autodimp h hyp); eauto with slow.
  { rw @free_vars_cterm; sp. }
  unfold reduces_toc.
  rw @get_cterm_force_int_bound_F_c; auto.
Qed.

Definition agree_upto_c {o} lib b (f g : @CTerm o) :=
  forall (i : Z),
    Z.abs_nat i < b
    -> {v1 : CTerm
       & {v2 : CTerm
        & reduces_toc lib (mkc_apply f (mkc_integer i)) v1
        # reduces_toc lib (mkc_apply g (mkc_integer i)) v2
        # alphaeqc v1 v2}}.

Lemma comp_force_int_app_F3_c_2 {o} :
  forall lib (F f g : @CTerm o) x z b,
    agree_upto_c lib b f g
    -> reduces_toc
         lib
         (force_int_bound_F_c x b F f (mkc_vbot x))
         (mkc_integer z)
    -> reduces_toc
         lib
         (force_int_bound_F_c x b F g (mkc_vbot x))
         (mkc_integer z).
Proof.
  introv agree r.
  allunfold @reduces_toc.
  allrw @get_cterm_force_int_bound_F_c.
  allsimpl.
  apply (comp_force_int_app_F3_2 lib (get_cterm F) (get_cterm f) (get_cterm g)); auto;
  allrw @free_vars_cterm; allsimpl; tcsp; eauto with slow.
  introv j; apply agree in j.
  exrepnd.
  exists (get_cterm v1) (get_cterm v2).
  destruct_cterms.
  allunfold @reduces_toc; allsimpl.
  allunfold @alphaeqc; allsimpl.
  clear agree.
  allapply @closed_if_isprog.
  rw i3.
  rw i2.
  dands; auto.
Qed.

Lemma comp_force_int_app_F2_c {o} :
  forall lib (F g : @CTerm o) x z b,
    reduces_toc
      lib
      (force_int_bound_F_c x b F g (mkc_vbot x))
      (mkc_integer z)
    -> reduces_toc
         lib
         (force_int_F_c x F g)
         (mkc_integer z).
Proof.
  introv r.
  allunfold @reduces_toc.
  allrw @get_cterm_force_int_bound_F_c.
  allrw @get_cterm_force_int_F_c.
  allsimpl.
  apply (comp_force_int_app_F2 lib (get_cterm F) (get_cterm g) x z b); auto;
  allrw @free_vars_cterm; allsimpl; tcsp; eauto with slow.
Qed.

Lemma mkcv_cont1_mkcv_apply {o} :
  forall v (t1 t2 : @CVTerm o [v,v]),
    mkcv_cont1 v (mkcv_apply [v,v] t1 t2)
    = mkcv_apply [v] (mkcv_cont1 v t1) (mkcv_cont1 v t2).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma mkcv_cont1_mk_cv {o} :
  forall v (t : @CTerm o),
    mkcv_cont1 v (mk_cv [v,v] t)
    = mk_cv [v] t.
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma mkcv_cont1_mk_cv_app_r {o} :
  forall v (t : @CVTerm o [v]),
    mkcv_cont1 v (mk_cv_app_r [v] [v] t)
    = t.
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma equality_force_int_f_c_T {o} :
  forall lib (f : @CTerm o) T,
    member lib f (mkc_fun mkc_int T)
    -> equality lib f (force_int_f_c nvarx f) (mkc_fun mkc_int T).
Proof.
  introv m.
  allrw @equality_in_fun; repnd; dands; auto.
  introv e.

  allrw @equality_in_int.
  allunfold @equality_of_int.
  exrepnd; spcast.

  pose proof (m (mkc_integer k) (mkc_integer k)) as h.
  autodimp h hyp.
  { apply equality_in_int.
    exists k.
    dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e1]
    |].
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        exact e0]
    |].

  clear dependent a.
  clear dependent a'.

  unfold force_int_f_c.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_cbv_substc_same.
  unfold force_int_cv.
  rw @mkcv_add_substc.
  rw @mkc_var_substc.
  rw @mkcv_zero_substc.

  eapply equality_respects_cequivc_right;
    [apply simpl_cequivc_mkc_cbv;
      apply cequivc_sym;
      apply cequivc_mkc_add_integer|].
  rw <- Zplus_0_r_reverse.

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;
      apply reduces_toc_implies_cequivc;
      apply reduces_toc_mkc_cbv_val;
      eauto 3 with slow|].

  rw @mkcv_cont1_mkcv_apply.
  rw @mkcv_apply_substc.
  rw @mkcv_cont1_mk_cv.
  rw @csubst_mk_cv.
  rw @mkcv_cont1_mk_cv_app_r.
  rw @mkc_var_substc.
  auto.
Qed.

Definition agree_upto_red_bc_T {o} lib b (f g : @CTerm o) T :=
  forall (t1 t2 : CTerm) (i : Z),
    reduces_toc lib t1 (mkc_integer i)
    -> reduces_toc lib t2 (mkc_integer i)
    -> Z.abs_nat i < b
    -> equality lib (mkc_apply f t1) (mkc_apply g t2) T.

Definition simple_eq_type {o} lib (T : @CTerm o) :=
  forall a b,
    equality lib a b T
    -> {v1 : CTerm
        & {v2 : CTerm
        & reduces_toc lib a v1
        # reduces_toc lib b v2
        # alphaeqc v1 v2 }}.

Lemma agree_upto_red_bc_T_implies_agree_upto_c {o} :
  forall lib b (f g : @CTerm o) T,
    simple_eq_type lib T
    -> agree_upto_red_bc_T lib b f g T
    -> agree_upto_c lib b f g.
Proof.
  introv spe agree j.
  pose proof (agree (mkc_integer i) (mkc_integer i) i) as h.
  repeat (autodimp h hyp); try (apply reduces_toc_refl).
Qed.

Definition continuous_T {o} lib (F : @CTerm o) T :=
  forall f,
    member lib f (mkc_fun mkc_int T)
    -> {b : nat
        & forall g,
            member lib g (mkc_fun mkc_int T)
            -> agree_upto_red_bc_T lib b f g T
            -> equality_of_int_tt lib (mkc_apply F f) (mkc_apply F g)}.

(*

  F f -> z
  => (* by typing *)
  F (\x.let x:=(x + 0) in f(x)) -> z
  => (* by comp_force_int_app_F *)
  exists b. forall e.
    F (\x.let x:=(let x:=x in if |x|<b then x else e) in f(x)) -> z
    => (* if e cannot get caught, because the 2 functions agree upto b *)
    F (\x.let x:=(let x:=x in if |x|<b then x else e) in g(x)) -> z
    => (* comp_force_int_app_F2 *)
    F (\x.let x:=(x + 0) in g(x)) -> z
    => (* by typing *)
    F g -> z

*)
Lemma continuity_axiom_v2 {o} :
  forall lib (F : @CTerm o) T,
    simple_eq_type lib T
    -> member lib F (mkc_fun (mkc_fun mkc_int T) mkc_int)
    -> continuous_T lib F T.
Proof.
  introv spe mT mt.

  assert (member lib (mkc_apply F f) mkc_int) as ma.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  (* by typing *)
  assert (equality lib f (force_int_f_c nvarx f) (mkc_fun mkc_int T)) as ea.
  { apply equality_force_int_f_c_T; auto. }

  assert (equality lib  (mkc_apply F f) (mkc_apply F (force_int_f_c nvarx f)) mkc_int) as mb.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  apply equality_in_int in mb.
  apply equality_of_int_imp_tt in mb.
  unfold equality_of_int_tt in mb; exrepnd; GC.

  (* 1st step *)
  pose proof (comp_force_int_app_F_c lib F f nvarx k) as step1.
  autodimp step1 hyp.
  { rw @computes_to_valc_iff_reduces_toc in mb0; repnd; auto. }
  destruct step1 as [b step1].

  exists b.
  introv mg agree.

  (* 2nd step *)
  pose proof (comp_force_int_app_F3_c_2 lib F f g nvarx k b) as step2.
  repeat (autodimp step2 hyp).
  { apply agree_upto_red_bc_T_implies_agree_upto_c in agree; auto. }

  (* 3rd step *)
  pose proof (comp_force_int_app_F2_c lib F g nvarx k b) as step3.
  repeat (autodimp step3 hyp).

  (* by typing *)
  assert (equality lib g (force_int_f_c nvarx g) (mkc_fun mkc_int T)) as eb.
  { apply equality_force_int_f_c_T; auto. }

  assert (equality lib (mkc_apply F g) (mkc_apply F (force_int_f_c nvarx g)) mkc_int) as mc.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  apply equality_in_int in mc.
  apply equality_of_int_imp_tt in mc.
  unfold equality_of_int_tt in mc; exrepnd; GC.

  assert (computes_to_valc lib (force_int_F_c nvarx F g) (mkc_integer k)) as c.
  { rw @computes_to_valc_iff_reduces_toc; dands; eauto with slow. }

  repeat computes_to_eqval.

  exists k0; dands; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
