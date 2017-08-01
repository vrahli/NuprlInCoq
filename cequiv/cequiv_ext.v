(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Export approx_ext_star.
Require Export computation7.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(* --------- DEFINITIONS --------- *)


(** Finally, we use [approx] to define the following equivalence
    relation on closed terms.

 *)

Definition cequiv_ext {p} lib (a b : @NTerm p) :=
  approx_ext lib a b # approx_ext lib b a.

(* begin hide *)
(*
(* open version of cequiv_ext *)
Definition cequiv_exto (a b : NTerm) :=
  approx_ext_open a b # approx_ext_open b a.
*)

(*
(** open version of cequiv_ext on wf terms *)
Definition cequiv_extow (a b : WTerm) :=
  cequiv_exto (get_wterm a) (get_wterm b).
*)

(*
(** cequiv_ext on wf terms *)
Definition cequiv_extw (a b : WTerm) :=
  cequiv_ext (get_wterm a) (get_wterm b).
 *)

(* end hide *)

(**
  We lift [cequiv_ext] to the [CTerm] type in the standard way:
 *)

Definition cequivc_ext {p} lib (a b : @CTerm p) :=
  cequiv_ext lib (get_cterm a) (get_cterm b).

(* begin hide *)

(** open version of cequiv_ext *)

Definition cequiv_ext_open {p} lib := olift (@cequiv_ext p lib).

(** bterm version of cequiv_ext *)

Definition bcequiv_ext {p} lib := blift (@cequiv_ext_open p lib).

(** bterms version of cequiv_ext *)

Definition cequiv_ext_bts {p} lib := lblift (@cequiv_ext_open p lib).

Ltac unfoldlift :=
  match goal with
    | [ H : context[approx_ext_open _ _ _] |- _ ] => unfold approx_ext_open in H
    | [ H : context[approx_ext_open _] |- _ ] => unfold approx_ext_open in H
    | [ H : context[cequiv_ext_open _ _ _] |- _ ] => unfold cequiv_ext_open in H
    | [ H : context[cequiv_ext_open _] |- _ ] => unfold cequiv_ext_open in H
    | [ H : context[bcequiv_ext _ _ _] |- _ ] => unfold bcequiv_ext in H
    | [ H : context[cequiv_ext_bts _ _ _] |- _ ] => unfold cequiv_ext_bts in H
    | [ H : context[approx_ext_bts _ _ _] |- _ ] => unfold approx_ext_bts in H
    | [ H : context[approx_ext_open_bterm _ _ _] |- _ ] => unfold approx_ext_open_bterm in H

    | [ |- context[approx_ext_open _ _ _] ] => unfold approx_ext_open
    | [ |- context[approx_ext_open _] ] => unfold approx_ext_open
    | [ |- context[cequiv_ext_open _ _ _] ] => unfold cequiv_ext_open
    | [ |- context[cequiv_ext_open _] ] => unfold cequiv_ext_open
    | [ |- context[bcequiv_ext _ _ _] ] => unfold bcequiv_ext
    | [ |- context[cequiv_ext_bts _ _ _] ] => unfold cequiv_ext_bts
    | [ |- context[approx_ext_bts _ _ _] ] => unfold approx_ext_bts
    | [ |- context[approx_ext_open_bterm _ _ _] ] => unfold approx_ext_open_bterm
  end.

Ltac unfoldlifts := repeat unfoldlift.

Lemma fold_cequiv_ext_open {p} :
  forall lib, olift (@cequiv_ext p lib) = cequiv_ext_open lib.
Proof. sp. Qed.

Ltac foldlift :=
  match goal with
    | [ H : context[olift (cequiv_ext ?lib) _ _] |- _ ] => fold (cequiv_ext_open lib) in H
    | [ H : context[blift (cequiv_ext_open ?lib) _ _] |- _ ] => fold (bcequiv_ext lib) in H

    | [ |- context[olift (cequiv_ext ?lib) _ _] ] => fold (cequiv_ext_open lib)
    | [ |- context[blift (cequiv_ext_open ?lib) _ _] ] => fold (bcequiv_ext lib)
  end.

Ltac foldlifts := repeat foldlift.

Lemma fold_test {p} :
  forall lib a b, olift (@cequiv_ext p lib) a b.
Proof.
  introv.
  foldlifts.
Abort.


(*
(** bterm version of cequiv_ext on wf terms *)
Definition bcequiv_extw (vs1 : list NVar) (t1 : WTerm) (vs2 : list NVar) (t2 : WTerm) :=
  bcequiv_ext (bterm vs1 (get_wterm t1)) (bterm vs2 (get_wterm t2)).
*)

(** bterm version of cequiv_ext on wf cterms *)
Definition bcequivc_ext {p}
           (lib : library)
           (vs1 : list NVar)
           (t1  : @CVTerm p vs1)
           (vs2 : list NVar)
           (t2  : CVTerm vs2) :=
  bcequiv_ext lib (bterm vs1 (get_cvterm vs1 t1)) (bterm vs2 (get_cvterm vs2 t2)).


(* --------- LEMMAS --------- *)

(* end hide *)
(** % \noindent % The equivalence of 
  [cequiv_ext] is a trivial consequence of either
  its symmetrical definition, or the corresponding
  properties of [approx_ext].

*)

Lemma cequiv_ext_refl {p} :
  forall lib t,
    @isprogram p t
    -> cequiv_ext lib t t.
Proof.
  unfold cequiv_ext; sp; apply approx_ext_refl; sp.
Qed.
(* begin hide *)

Lemma cequivc_ext_refl {p} :
  forall lib t,
    @cequivc_ext p lib t t.
Proof.
  intro; destruct t; unfold cequivc_ext; simpl.
  apply cequiv_ext_refl; rw @isprogram_eq; sp.
Qed.
Hint Immediate cequivc_ext_refl.

Lemma cequiv_ext_wf_term {p} :
  forall lib a b,
    @cequiv_ext p lib a b -> wf_term a # wf_term b.
Proof.
  intros. unfold cequiv_ext in X; sp; apply approx_ext_wf_term in X0; sp.
Qed.

Lemma cequiv_ext_isprog {p} :
  forall lib a b,
    @cequiv_ext p lib a b -> isprog a # isprog b.
Proof.
  intros. unfold cequiv_ext in X; sp; apply approx_ext_isprog in X0; sp.
Qed.

Lemma cequiv_ext_isprogram {p} :
  forall lib a b,
    @cequiv_ext p lib a b -> isprogram a # isprogram b.
Proof.
  introv Hc. apply cequiv_ext_isprog in Hc.
  repnd; split; apply isprogram_eq; auto.
Qed.

Lemma cequiv_ext_le_approx_ext {p} :
  forall lib, le_bin_rel (cequiv_ext lib) (@approx_ext p lib).
Proof.
  unfold le_bin_rel, cequiv_ext.
  spc.
Qed.

Lemma iff_l: forall A B,
  (A <=> B) -> (A ->B).
Proof.
 introv X; apply X; auto.
Qed.

Lemma iff_r: forall A B,
  (A <=> B) -> (B ->A).
Proof.
 introv X; apply X; auto.
Qed.


Lemma bcequiv_ext_wf_term {p} :
  forall lib vs1 vs2 a b,
    bcequiv_ext lib (bterm vs1 a) (@bterm p vs2 b) -> wf_term a # wf_term b.
Proof.
  introv bc.
  repnud bc.
  apply (le_blift_olift _ _ (cequiv_ext_le_approx_ext lib)) in bc.
  apply approxbt_btwf in bc.
  repnd.
  invertsn bc.
  invertsn bc0.
  split; eauto with slow.
Qed.

Lemma bcequiv_ext_isprog {p} :
  forall lib vs1 vs2 a b,
    bcequiv_ext lib (bterm vs1 a) (@bterm p vs2 b)
    -> isprog_vars vs1 a # isprog_vars vs2 b.
Proof.

(**
  intros.
  repeat (rewrite isprog_vars_eq).
  repeat (rewrite nt_wf_eq).
  assert (subvars (free_vars a) vs1 # subvars (free_vars b) vs2);
    try (complete (applydup bcequiv_ext_wf_term in X; sp;
                   apply isprog_vars_eq; sp;
                   apply nt_wf_eq; auto)).

  unfold bcequiv_ext, blift in X; repd.
  allrewrite num_bvars_on_bterm.

  generalize (c (map (fun v => mk_axiom) vs1)); intros.
  generalize (c (map (fun v => mk_axiom) vs2)); intros.
  allrewrite map_length.
  allunfold apply_bterm.
  allsimpl.

  dimp X;  auto; try (intros; allrw in_map_iff; exrepd; subst; apply isprogram_axiom).
  dimp X0; auto; try (intros; allrw in_map_iff; exrepd; subst; apply isprogram_axiom).
  allrewrite combine_vars_map.
  apply cequiv_ext_isprog in hyp; repd.
  apply cequiv_ext_isprog in hyp0; repd.
  allrw isprog_eq.
  allunfold isprogram; allunfold closed; repd.
  rewrite isprogram_lsubst2 in e3.
  rewrite isprogram_lsubst2 in e0.
  rw <- null_iff_nil in e3.
  rw <- null_iff_nil in e0.
  rw null_remove_nvars_subvars in e3.
  rw null_remove_nvars_subvars in e0.
  rw dom_sub_map_axiom in e3.
  rw dom_sub_map_axiom in e0; sp.
  sp; allrw in_map_iff; sp; inj; sp.
  sp; allrw in_map_iff; sp; inj; sp.
*)
Abort. (** not true anymore ?*)

(* end hide *)
Lemma cequiv_ext_sym {p} :
  forall lib a b,
    @cequiv_ext p lib a b <=> cequiv_ext lib b a.
Proof.
  unfold cequiv_ext; sp; split; sp.
Qed.
(* begin hide *)

(*
Lemma cequiv_extw_sym :
  forall a b,
    cequiv_extw a b <=> cequiv_extw b a.
Proof.
  unfold cequiv_extw, cequiv_ext; sp; split; sp.
Qed.
*)

(*
Lemma cequiv_extow_sym :
  forall a b,
    cequiv_extow a b <=> cequiv_extow b a.
Proof.
  unfold cequiv_extow, cequiv_exto; sp; split; sp.
Qed.
*)

Lemma cequivc_ext_sym {p} :
  forall lib a b,
    @cequivc_ext p lib a b <=> cequivc_ext lib b a.
Proof.
  unfold cequivc_ext; sp; split; sp; apply cequiv_ext_sym; auto.
Qed.

(* end hide *)
Lemma cequiv_ext_trans {p} :
  forall lib a b c,
    @cequiv_ext p lib a b
    -> cequiv_ext lib b c
    -> cequiv_ext lib a c.
Proof.
  unfold cequiv_ext; sp; apply @approx_ext_trans with (b := b); auto.
Qed.
(* begin hide *)

(*
Lemma cequiv_extw_trans :
  forall a b c,
    cequiv_extw a b
    -> cequiv_extw b c
    -> cequiv_extw a c.
Proof.
  unfold cequiv_extw, cequiv_ext; sp; apply approx_ext_trans with (b := get_wterm b); auto.
Qed.
*)

(*
Lemma cequiv_extow_trans :
  forall a b c,
    cequiv_extow a b
    -> cequiv_extow b c
    -> cequiv_extow a c.
Proof.
  unfold cequiv_extow, cequiv_exto; sp; apply approx_ext_open_trans with (b := get_wterm b); auto.
Qed.
*)

Lemma cequivc_ext_trans {p} :
  forall lib a b c,
    @cequivc_ext p lib a b
    -> cequivc_ext lib b c
    -> cequivc_ext lib a c.
Proof.
  unfold cequivc_ext; sp; apply @cequiv_ext_trans with (b := get_cterm b); auto.
Qed.

(*
Lemma approx_extw_cequiv_extw_trans :
  forall a b c,
    approx_extw a b
    -> cequiv_extw b c
    -> approx_extw a c.
Proof.
  destruct a; destruct b; destruct c.
  unfold cequiv_extw, cequiv_ext, approx_extw; sp; allsimpl.
  apply approx_ext_trans with (b := x0); auto.
Qed.
*)

Lemma approxc_ext_cequivc_ext_trans {p} :
  forall lib a b c,
    @approxc_ext p lib a b
    -> cequivc_ext lib b c
    -> approxc_ext lib a c.
Proof.
  destruct a; destruct b; destruct c.
  unfold cequivc_ext, cequiv_ext, approxc_ext; sp; allsimpl.
  apply approx_ext_trans with (b := x0); auto.
Qed.

(*
Lemma cequiv_extw_approx_extw_trans :
  forall a b c,
    cequiv_extw a b
    -> approx_extw b c
    -> approx_extw a c.
Proof.
  destruct a; destruct b; destruct c.
  unfold cequiv_extw, cequiv_ext, approx_extw; sp; allsimpl.
  apply approx_ext_trans with (b := x0); auto.
Qed.
*)

Lemma cequivc_ext_approxc_ext_trans {p} :
  forall lib a b c,
    @cequivc_ext p lib a b
    -> approxc_ext lib b c
    -> approxc_ext lib a c.
Proof.
  destruct a; destruct b; destruct c.
  unfold cequivc_ext, cequiv_ext, approxc_ext; sp; allsimpl.
  apply approx_ext_trans with (b := x0); auto.
Qed.

(*
Lemma cequiv_extw_approx_extw_trans2 :
  forall a b c,
    cequiv_extw b a
    -> approx_extw b c
    -> approx_extw a c.
Proof.
  destruct a; destruct b; destruct c.
  unfold cequiv_extw, cequiv_ext, approx_extw; sp.
  apply approx_ext_trans with (b := x0); auto.
Qed.
*)

Lemma olift_approx_ext_cequiv_ext {p} :
  forall lib t1 t2,
    @approx_ext_open p lib t1 t2
    -> approx_ext_open lib t2 t1
    -> cequiv_ext_open lib t1 t2.
Proof.
  unfold approx_ext_open, cequiv_ext_open, olift, cequiv_ext.
  spc.
Qed.

Lemma olift_cequiv_ext_approx_ext {p} :
  forall lib t1 t2,
    @cequiv_ext_open p lib t1 t2
    -> approx_ext_open lib t2 t1 # approx_ext_open lib t1 t2.
Proof.
  unfold cequiv_ext_open, approx_ext_open, olift, cequiv_ext.
  introns Hc. exrepnd. dands;spcf;
  introv Hwf H1pr H2pr;
  apply Hc in Hwf;sp.
Qed.



Hint Resolve alpha_eq_bterm_lenbvars : slow.

Lemma blift_cequiv_ext_approx_ext {p} :
  forall lib bt1 bt2,
    @bcequiv_ext p lib bt1 bt2
    -> approx_ext_open_bterm lib bt2 bt1 # approx_ext_open_bterm lib bt1 bt2.
Proof.
  unfoldlifts.
  unfold blift.
  introv Hcb.
  exrepnd. apply olift_cequiv_ext_approx_ext in Hcb1.
  exrepnd. dands; eexists; eexists; eexists; eauto.
      (* (* info eauto : *)
      apply pair.
       exact Hcb3.
       apply pair.
        exact Hcb0.
        exact Hcb2.
      (* info eauto : *)
      apply pair.
       exact Hcb1.
       apply pair.
        exact Hcb2.
        exact Hcb0. *)

Qed.


Lemma blift_approx_ext_cequiv_ext {p} :
  forall lib bt1 bt2,
    @approx_ext_open_bterm p lib bt1 bt2
    -> approx_ext_open_bterm lib bt2 bt1
    -> bcequiv_ext lib bt1 bt2.
Proof.
  unfoldlifts.
  unfold blift. introv H1b H2b.
  exrepnd.
  pose proof (fresh_vars (length lv) (all_vars nt1 
      ++ all_vars nt2 ++ all_vars nt0 ++ all_vars nt3)) as Hfr.
  exrepnd.
  assert (alpha_eq_bterm (bterm lv nt2) (bterm lv0 nt0)) as XX
  by eauto with slow.
  apply alpha_eq_bterm_lenbvars in XX.

  

  dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn H1b0 H1b2); 
    try(rename hyp into H1c); exrepnd; spc; eauto 3 with slow;[| disjoint_reasoningv].
  dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn H2b0 H2b2);
     try(rename hyp into H2c);
    exrepnd;spc;[| disjoint_reasoningv;fail].

  exists lvn.
  eexists;
  eexists;
  split; eauto.
  pose proof (alpha_eq_bterm_trans _ _ _
    (alpha_eq_bterm_sym _ _ H2c3)
      H1c4
    ) as H1al.

  pose proof (alpha_eq_bterm_trans _ _ _
    (alpha_eq_bterm_sym _ _ H2c4)
      H1c3
    ) as H2al.
    
    clear H2c4 H2c3 H1c4 H1c3 H2b0 H2b2 H1b0 H1b2.
  apply alpha_eq_bterm_triv in H1al.
  apply alpha_eq_bterm_triv in H2al.

  apply (approx_ext_open_alpha_rw_r _ _ _ _ H2c0) in H2b1.
  apply (approx_ext_open_alpha_rw_l _ _ _ _ H2c2) in H2b1.
  rename H2b1 into H1ao.

  apply (approx_ext_open_alpha_rw_r _ _ _ _ H1c0) in H1b1.
  apply (approx_ext_open_alpha_rw_l _ _ _ _ H1c2) in H1b1.
  rename H1b1 into H2ao.


  
  apply approx_ext_open_lsubst with (lvi:=lv) 
      (lvo:=lvn) in H1ao.

  apply approx_ext_open_lsubst with (lvi:=lv0) 
      (lvo:=lvn) in H2ao.

  apply (approx_ext_open_alpha_rw_l _ _ _ _ (alpha_eq_sym _ _ H1al)) in H2ao.
  apply (approx_ext_open_alpha_rw_r _ _ _ _ (alpha_eq_sym _ _ H2al)) in H2ao.
  apply olift_approx_ext_cequiv_ext; spc.
Qed.

Lemma lblift_cons {p} :
  forall R bt1 bt2 bts1 bts2,
    @lblift p R (bt1 :: bts1) (bt2 :: bts2)
    <=> (blift R bt1 bt2 # lblift R bts1 bts2).
Proof.
  unfold lblift; simpl; sp; split; sp.
  assert (0 < S (length bts1)) by omega.
  apply X in H.
  allrewrite @selectbt_cons; allsimpl; auto.
  assert (S n < S (length bts1)) by omega.
  apply X in H0.
  allrewrite @selectbt_cons; allsimpl; auto.
  allrewrite minus0; auto.
  repeat (rewrite selectbt_cons).
  destruct n; allsimpl; auto.
  allrewrite minus0.
  assert (n < length bts1) by omega.
  apply X in H0; auto.
Qed.

Lemma lblift_approx_ext_cequiv_ext {p} :
  forall lib bterms1 bterms2,
    @approx_ext_bts p lib bterms1 bterms2
    -> approx_ext_bts lib bterms2 bterms1
    -> cequiv_ext_bts lib bterms1 bterms2.
Proof.
  unfoldlifts.
  induction bterms1; simpl; sp.
  destruct bterms2; allunfold @lblift; allsimpl; sp; omega.
  destruct bterms2.
  allunfold @lblift; allsimpl; sp; omega.
  generalize (lblift_cons (olift (approx_ext lib)) a b bterms1 bterms2).
  generalize (lblift_cons (olift (approx_ext lib)) b a bterms2 bterms1).
  generalize (lblift_cons (olift (cequiv_ext lib)) a b bterms1 bterms2).
  intros e1 e2 e3.
  trewrite e3 in X; clear e3.
  trewrite e2 in X0; clear e2.
  trewrite e1; clear e1; sp.
  apply blift_approx_ext_cequiv_ext; auto.
Qed.

Lemma cequiv_ext_canonical_form {pp} :
  forall lib t t' op bterms,
    computes_to_value lib t (oterm (Can op) bterms)
    -> cequiv_ext lib t t'
    -> {bterms' : list (@BTerm pp)
        & computes_to_value lib t' (oterm (Can op) bterms')
        # cequiv_ext_bts lib bterms bterms'}.
Proof.
  sp; allunfold @cequiv_ext; sp.
  apply @approx_ext_canonical_form with (op := op) (bterms := bterms) in X1; sp.
  apply @approx_ext_canonical_form with (op := op) (bterms := bterms') in X0; sp.
  apply @computes_to_value_eq with (v2 := oterm (Can op) bterms) in p2; auto.
  inversion p2; subst.
  exists bterms'; sp.
  apply lblift_approx_ext_cequiv_ext; auto.
Qed.

Lemma cequivc_ext_canonical_form {p} :
  forall lib t t' op bterms,
    computes_to_valuec lib t (oterm (Can op) bterms)
    -> cequivc_ext lib t t'
    -> {bterms' : list (@BTerm p)
        & computes_to_valuec lib t' (oterm (Can op) bterms')
        # cequiv_ext_bts lib bterms bterms'}.
Proof.
  sp; allunfold @cequivc_ext; allunfold @computes_to_valuec; sp; destruct t, t'; allsimpl.
  apply cequiv_ext_canonical_form with (t' := x0) in X; sp.
Qed.


Lemma cequiv_ext_exception_weak {pp} :
  forall lib t a e t' ,
    (t =e>( a, lib)e)
    -> cequiv_ext lib t t'
    -> {a' : @NTerm pp &
       { e' : NTerm &
        computes_to_exception lib a' t' e'
        }}.
Proof.
  introv ce sim. unfold cequiv_ext in sim. destruct sim as [a1 a2]. 
  dup ce as cd.
  eapply @exception_approx_ext in cd;[exrepnd | exact a1]. 
  exists a' e'. auto. 
Qed.



(*
Lemma cequiv_exto_canonical_form :
  forall t t' op bterms,
    computes_to_value t (oterm (Can op) bterms)
    -> cequiv_exto t t'
    -> exists bterms',
         computes_to_value t' (oterm (Can op) bterms')
         # lblift cequiv_exto bterms bterms'.
Proof.
  sp; allunfold cequiv_exto; sp.
  apply approx_ext_canonical_form with (op := op) (bterms := bterms) in H0; sp.
  apply approx_ext_canonical_form with (op := op) (bterms := bterms') in H1; sp.
  apply computes_to_value_eq with (v2 := oterm (Can op) bterms) in H1; auto.
  inversion H1; subst.
  exists bterms'; sp.
  apply lblift_approx_ext_cequiv_ext; auto.
Qed.
*)
Lemma alpha_implies_cequiv_ext {p} :
  forall lib nt1 nt2,
    isprogram nt1
    -> @isprogram p nt2
    -> alpha_eq nt1 nt2
    -> cequiv_ext lib nt1 nt2.
Proof.
  introv ip1 ip2 aeq.
  unfold cequiv_ext; sp.
  apply alpha_implies_approx_ext; sp.
  apply alpha_implies_approx_ext; sp.
  apply alpha_eq_sym; sp.
Qed.

Hint Resolve alpha_implies_cequiv_ext cequiv_ext_sym cequiv_ext_trans : slow.

Lemma cequiv_ext_sym_eauto {p} :
   forall lib (a b : @NTerm p), cequiv_ext lib a b -> cequiv_ext lib b a.
Proof.
  introv.
  apply cequiv_ext_sym.
Qed.

Hint Resolve cequiv_ext_sym_eauto : slow.






Lemma cequiv_ext_rw_l {p} : forall lib a a',
  @alpha_eq p a a'
  -> forall b, (cequiv_ext lib a b <=> cequiv_ext lib a' b).
Proof.
  introv Hal. intros.
  split; introv Hyp; applydup @cequiv_ext_isprogram in Hyp; repnd; alpha_hyps Hal;
  allunfold @cequiv_ext; repnd; dands; eauto with slow slowbad.
Qed.


Lemma cequiv_ext_rw_l_eauto {p} : forall lib a a',
  @alpha_eq p a a'
  -> forall b, (cequiv_ext lib a b -> cequiv_ext lib a' b).
Proof.
  introv Hal. apply cequiv_ext_rw_l. eauto with slow.
Qed.


Lemma cequiv_ext_rw_r {p} : forall lib a a',
  @alpha_eq p a a'
  -> forall b, (cequiv_ext lib b a <=> cequiv_ext lib b a').
Proof.
  introv Hal. intros.
  split; introv Hyp; applydup @cequiv_ext_isprogram in Hyp; repnd; alpha_hyps Hal;
  allunfold @cequiv_ext; repnd; dands; eauto with slow slowbad.
Qed.

Lemma cequiv_ext_rw_r_eauto {p} : forall lib a a',
  @alpha_eq p a a'
  -> forall b, (cequiv_ext lib b a -> cequiv_ext lib b a').
Proof.
  introv Hal. apply cequiv_ext_rw_r. eauto with slow.
Qed.

Hint Resolve cequiv_ext_rw_l_eauto cequiv_ext_rw_r_eauto : slow.

Lemma respects_alpha_cequiv_ext {p} : forall lib, respects_alpha (@cequiv_ext p lib).
Proof.
  split.
  - introv Hal.  apply cequiv_ext_rw_l_eauto; auto.
  - introv Hal H1c. allunfold @cequiv_ext. repnd.
    rwhg Hal H1c.
    rwhg Hal H1c0.
    dands; auto.
Qed.

Hint Resolve respects_alpha_cequiv_ext : respects.

Lemma olift_cequiv_ext_rw_l_eauto {p} : forall lib a a',
  @alpha_eq p a a'
  -> forall b, cequiv_ext_open lib a b -> cequiv_ext_open lib a' b.
Proof.
  unfoldlifts.
  introv Hal Hoc.
  rwhg Hal Hoc; auto.
Qed.

Lemma olift_cequiv_ext_rw_r_eauto {p} : forall lib a a',
  @alpha_eq p a a'
  -> forall b, cequiv_ext_open lib b a -> cequiv_ext_open lib b a'.
Proof.
  unfoldlifts.
  introv Hal Hoc.
  rwhg Hal Hoc; auto.
Qed.

Hint Resolve olift_cequiv_ext_rw_l_eauto olift_cequiv_ext_rw_r_eauto : slow.


Lemma lblift_cequiv_ext3 {p} :
  forall lib a b c bterms,
    cequiv_ext_bts lib [nobnd a, nobnd b, nobnd c] bterms
    -> {a', b', c' : @NTerm p
        $ bterms = [nobnd a', nobnd b', nobnd c']
        # cequiv_ext_open lib a a'
        # cequiv_ext_open lib b b'
        # cequiv_ext_open lib c c'}.
Proof.
  unfoldlifts.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold @nobnd.
  repeat(alpharelbtd).
  foldlifts.
  eexists; eexists; eexists; dands; try reflexivity; eauto 4 with slow.
Qed.

Lemma lblift_cequiv_ext2 {p} :
  forall lib a b bterms,
    cequiv_ext_bts lib [nobnd a, nobnd b] bterms
    -> {c, d : @NTerm p
        $ bterms = [nobnd c, nobnd d]
        # cequiv_ext_open lib a c
        # cequiv_ext_open lib b d}.
Proof.
  unfoldlifts.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold @nobnd.
  repeat(alpharelbtd).
  foldlifts.
  eexists; eexists; dands; try reflexivity; eauto 4 with slow.
Qed.


Lemma lblift_cequiv_ext1 {p} :
  forall lib a bterms,
    cequiv_ext_bts lib [nobnd a] bterms
    -> {b : @NTerm p & bterms = [nobnd b] # cequiv_ext_open lib a b}.
Proof.
  unfoldlifts.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold @nobnd.
  repeat(alpharelbtd).
  exists nt0.
  dands; spc.

  foldlifts.
  eauto 4 with slow.
Qed.

Lemma lblift_cequiv_ext0 {p} :
  forall lib bterms,
    @cequiv_ext_bts p lib [] bterms
    -> bterms = [].
Proof.
  unfoldlifts; unfold lblift; simpl; destruct bterms; simpl; sp.
Qed.

Lemma lblift_cequiv_ext0l {p} :
  forall lib a l b bterms,
    cequiv_ext_bts lib [nobnd a, bterm l b] bterms
    -> {a' : NTerm & {l' : list NVar & {b' : @NTerm p &
         bterms = [nobnd a', bterm l' b']
         # cequiv_ext_open lib a a'
         # bcequiv_ext lib (bterm l b) (bterm l' b')}}}.
Proof.
  unfoldlifts.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold @nobnd.
  repeat(alpharelbtd).
  dest_bterms.
  foldlifts.
  eexists; eexists ; eexists; dands; try reflexivity; eauto 4 with slow.
  eexists; eexists ; eexists; dands; try reflexivity; eauto 4 with slow.
Qed.

Lemma lblift_cequiv_ext01 {p} :
  forall lib a v b bterms,
    cequiv_ext_bts lib [nobnd a, bterm [v] b] bterms
    -> {a' : NTerm & {v' : NVar & {b' : @NTerm p &
         bterms = [nobnd a', bterm [v'] b']
         # cequiv_ext_open lib a a'
         # bcequiv_ext lib (bterm [v] b) (bterm [v'] b')}}}.
Proof.
  unfoldlifts.
  unfold lblift; simpl; destruct bterms; simpl; sp.
  allunfold @nobnd.
  repeat(alpharelbtd).
  applydup @alphaeqbt1v2 in X1bt2.
  exrepnd ; subst.
  dest_bterms.
  apply alpha_eq_bterm_sym in X1bt0.
  applydup @alphaeqbt1v2 in X1bt0.
  exrepnd ; subst.
  exists nt4 v'0 n.
  dands; eauto; foldlifts.
  - eauto 4 with slow.
  - unfold bcequiv_ext, blift.
    exists [v'].
    eexists nt1; eexists nt2; dands; eauto with slow.
Qed.

Lemma cequiv_ext_int {o} :
  forall lib (T T' : @NTerm o),
    computes_to_value lib T mk_int
    -> cequiv_ext lib T T'
    -> computes_to_value lib T' mk_int.
Proof.
  sp.
  apply cequiv_ext_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv_ext0 in p; subst; auto.
Qed.

(*
Lemma cequiv_extw_int :
  forall T T',
    computes_to_valw T mkw_int
    -> cequiv_extw T T'
    -> computes_to_valw T' mkw_int.
Proof.
  sp.
  destruct T, T'.
  allunfold mkw_int.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_int with (T := x); auto.
Qed.
*)

Lemma cequivc_ext_int {o} :
  forall lib (T T' : @CTerm o),
    computes_to_valc lib T mkc_int
    -> cequivc_ext lib T T'
    -> computes_to_valc lib T' mkc_int.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_ext_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequiv_ext_uni {o} :
  forall lib (t t' : @NTerm o) n,
    computes_to_value lib t (mk_uni n)
    -> cequiv_ext lib t t'
    -> computes_to_value lib t' (mk_uni n).
Proof.
  sp.
  apply @cequiv_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.


(*
Lemma cequiv_extw_uni :
  forall t t' n,
    computes_to_valw t (mkw_uni n)
    -> cequiv_extw t t'
    -> computes_to_valw t' (mkw_uni n).
Proof.
  sp.
  destruct t, t'.
  allunfold mkw_nat.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_uni with (t := x); auto.
Qed.
*)

Lemma cequivc_ext_uni {o} :
  forall lib (t t' : @CTerm o) n,
    computes_to_valc lib t (mkc_uni n)
    -> cequivc_ext lib t t'
    -> computes_to_valc lib t' (mkc_uni n).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequiv_ext_integer {o} :
  forall lib (t t' : @NTerm o) n,
    computes_to_value lib t (mk_integer n)
    -> cequiv_ext lib t t'
    -> computes_to_value lib t' (mk_integer n).
Proof.
  sp.
  apply @cequiv_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

(*
Lemma cequiv_extw_integer :
  forall t t' n,
    computes_to_valw t (mkw_integer n)
    -> cequiv_extw t t'
    -> computes_to_valw t' (mkw_integer n).
Proof.
  sp.
  destruct t, t'.
  allunfold mkw_nat.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_integer with (t := x); auto.
Qed.
*)

Lemma cequivc_ext_integer {o} :
  forall lib (t t' : @CTerm o) n,
    computes_to_valc lib t (mkc_integer n)
    -> cequivc_ext lib t t'
    -> computes_to_valc lib t' (mkc_integer n).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequiv_ext_nat {o} :
  forall lib (t t' : @NTerm o) n,
    computes_to_value lib t (mk_nat n)
    -> cequiv_ext lib t t'
    -> computes_to_value lib t' (mk_nat n).
Proof.
  sp.
  apply @cequiv_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

(*
Lemma cequiv_extw_nat :
  forall t t' n,
    computes_to_valw t (mkw_nat n)
    -> cequiv_extw t t'
    -> computes_to_valw t' (mkw_nat n).
Proof.
  sp.
  destruct t, t'.
  allunfold mkw_nat.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_nat with (t := x); auto.
Qed.
*)

Lemma cequiv_ext_base {o} :
  forall lib (t t' : @NTerm o),
    computes_to_value lib t mk_base
    -> cequiv_ext lib t t'
    -> computes_to_value lib t' mk_base.
Proof.
  sp.
  apply @cequiv_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

(*
Lemma cequiv_extw_base :
  forall t t',
    computes_to_valw t mkw_base
    -> cequiv_extw t t'
    -> computes_to_valw t' mkw_base.
Proof.
  sp.
  destruct t, t'.
  allunfold mkw_base.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_base with (t := x); auto.
Qed.
*)

Lemma cequivc_ext_base {o} :
  forall lib (t t' : @CTerm o),
    computes_to_valc lib t mkc_base
    -> cequivc_ext lib t t'
    -> computes_to_valc lib t' mkc_base.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequiv_ext_axiom {o} :
  forall lib (t t' : @NTerm o),
    computes_to_value lib t mk_axiom
    -> cequiv_ext lib t t'
    -> computes_to_value lib t' mk_axiom.
Proof.
  sp.
  apply @cequiv_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

(*
Lemma cequiv_extw_axiom :
  forall t t',
    computes_to_valw t mkw_axiom
    -> cequiv_extw t t'
    -> computes_to_valw t' mkw_axiom.
Proof.
  sp.
  destruct t, t'.
  allunfold mkw_axiom.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_axiom with (t := x); auto.
Qed.
*)

Lemma cequivc_ext_axiom {o} :
  forall lib (t t' : @CTerm o),
    computes_to_valc lib t mkc_axiom
    -> cequivc_ext lib t t'
    -> computes_to_valc lib t' mkc_axiom.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_ext_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Theorem cequiv_ext_open_cequiv_ext {p} :
  forall lib t1 t2,
  isprogram t1
  -> @isprogram p t2
  -> cequiv_ext_open lib t1 t2
  ->  cequiv_ext lib t1 t2.
Proof.
  introv H1pr H2pr Hol.
  invertsna Hol Hol.
  exrepnd.
  assert (@wf_sub p [])  as Hwf by (apply sub_range_sat_nil).
  apply Hol0 in Hwf;allrw @lsubst_nil; auto.
Qed.

Ltac unfold_all_mk2 :=
    allunfold mk_apply;
    allunfold mk_bottom;
    allunfold mk_fix;
    allunfold mk_id;
    allunfold mk_lam;
    allunfold mk_var;
    allunfold mk_sup;
    allunfold mk_refl;
    allunfold mk_equality;
    allunfold mk_tequality;
    allunfold mk_cequiv;
    allunfold mk_approx;
    allunfold mk_exception;
    allunfold mk_outl;
    allunfold mk_outr;
    allunfold nobnd.

(**
Ltac prove_cequiv_ext_mk2 :=
  let Hcomp := fresh "Hcomp" in
  let Hcomp99 := fresh "Hcomp99" in
  let Hcomp1 := fresh "Hcomp1" in
  let Hcomp2 := fresh "Hcomp2" in
  let Hceq := fresh "Hceq" in
  introv Hcomp Hceq;
  applydup cequiv_ext_isprogram in Hceq; repnd;
  applydup preserve_program in Hcomp; auto;
  eapply cequiv_ext_canonical_form  in Hcomp; eauto; exrepnd;
  allunfold nobnd ;
  (match goal with
    | [H :lblift (olift cequiv_ext) [bterm [] _, bterm [_] _] _ |- _ ] =>
        apply lblift_cequiv_ext01 in Hcomp1; sp; subst
    | [H :lblift (olift cequiv_ext) [bterm [] _, bterm [] _] _ |- _ ] =>
        apply lblift_cequiv_ext2 in H; sp; subst
    | [H :lblift (olift cequiv_ext) [bterm [] _] _ |- _ ] =>
        apply lblift_cequiv_ext1 in H; sp; subst
    | [H :lblift (olift cequiv_ext) [bterm [] _, bterm [] _, bterm [] _] _ |- _ ] =>
        apply lblift_cequiv_ext3 in H; sp; subst
     end
   );
  applydup preserve_program in Hcomp2; auto;
  allunfold mk_approx; allunfold nobnd; unfold_all_mk2; repeat(decomp_progh);
  repeat match goal with 
  [ |-  sigT _  ] =>  eexists
  end; sp; eauto;apply cequiv_ext_open_cequiv_ext; 
      show_hyps; eauto 2 with slow;
     idtac "prove_cequiv_ext_mk failed - you might need to add something to unfold_all_mk2".
*)


Ltac prove_cequiv_ext_mk :=
  let Hcomp   := fresh "Hcomp" in
  let Hcomp1  := fresh "Hcomp1" in
  let Hcomp2  := fresh "Hcomp2" in
  let Hcomp3  := fresh "Hcomp3" in
  let Hcomp4  := fresh "Hcomp4" in
  let Hceq    := fresh "Hceq" in
  let bt      := fresh "bt" in
  let Hbt     := fresh "Hbt" in
  let bterms' := fresh "bterms'" in
  introv Hcomp Hceq;
    applydup @cequiv_ext_isprogram in Hceq; repnd;
    applydup @preserve_program in Hcomp as Hcomp1; auto;
    eapply @cequiv_ext_canonical_form in Hcomp; eauto;
    destruct Hcomp as [bterms' Hcomp];
    destruct Hcomp as [Hcomp2 Hcomp3];
    applydup @preserve_program in Hcomp2 as Hcomp4; auto;
    unfold_all_mk;
    unfold_all_mk2;
    match goal with
      | [H : lblift _ _ ?bterms'  |- _ ] =>
        unfold lblift in H; simpl in H;
        let Hlen := fresh H "len" in
        destruct H as [Hlen H];   dlist_len_name bterms' bt
      | [H : cequiv_ext_bts _ _ ?bterms' |- _ ] =>
        unfold cequiv_ext_bts, lblift in H; simpl in H;
        let Hlen := fresh H "len" in
        destruct H as [Hlen H];   dlist_len_name bterms' bt
    end;
  dforall_lt_hyp Hbt;
  allunfold @selectbt; allsimpl;
  destruct_bterms;
  blift_nums;
  allunfold @num_bvars; allsimpl;
  dlists_len;
  unfold_all_mk;
  unfold_all_mk2;
  repeat(decomp_progh3);
  remove_relbt_samevar;
  foldlifts;
  rep_eexists; dands; eauto; apply @cequiv_ext_open_cequiv_ext;
     eauto 2 with slow.

Lemma cequiv_ext_mk_approx {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_approx a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_approx a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk.
Qed.

(*
Lemma cequiv_extw_mkw_approx_ext :
  forall t t' a b,
    computes_to_valw t (mkw_approx_ext a b)
    -> cequiv_extw t t'
    -> {a', b' : WTerm &
         computes_to_valw t' (mkw_approx_ext a' b')
         # cequiv_extw a a'
         # cequiv_extw b b'}.
Proof.
  sp.
  destruct t, t', a, b.
  allunfold mkw_approx_ext.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_mk_approx with (t' := x0) in H; sp.
  applydup cequiv_ext_wf_term in p1.
  applydup cequiv_ext_wf_term in p; sp.
  exists (existT wf_term a' p2) (existT wf_term b' p3).
  simpl; sp.
Qed.
*)

Lemma cequivc_ext_mkc_approx {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_approx a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_approx a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_approx lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp isc]; subst.
  allrw <- @isprogram_approx_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

(*
Lemma lib_extends_preserves_approx_ext {o} :
  forall lib lib' (t1 t2 : @NTerm o),
    lib_extends lib' lib
    -> approx_ext lib t1 t2
    -> approx_ext lib' t1 t2.
Proof.
  cofix; introv ext ap.
  inversion ap as [cl].
  constructor.
  unfold close_compute_ext in *; repnd.
  dands; auto.

  - introv comp.

Qed.

Lemma lib_extends_preserves_approx_ext_open {o} :
  forall lib lib' (t1 t2 : @NTerm o),
    lib_extends lib' lib
    -> approx_ext_open lib t1 t2
    -> approx_ext_open lib' t1 t2.
Proof.
  introv ext ap.
  unfold approx_ext_open in *.
  unfold olift in *.
  repnd; dands; auto.
  introv wf isp1 isp2.
  applydup ap in wf; auto.
  SearchAbout olift.
Qed.

Lemma lib_extends_preserves_lblift_approx_ext_open {o} :
  forall lib lib' (l1 l2 : list (@BTerm o)),
    lib_extends lib' lib
    -> lblift (approx_ext_open lib) l1 l2
    -> lblift (approx_ext_open lib') l1 l2.
Proof.
  introv ext h.
  unfold lblift in *; repnd.
  dands; auto.
  introv q.
  applydup h in q.
  unfold blift in *; exrepnd.
  eexists; eexists; eexists; dands;[|eauto|eauto].

Qed.
*)

Lemma approx_ext_canonical_form2 {p} :
  forall lib t t' op bterms,
    computes_to_value lib t (oterm (Can op) bterms)
    -> approx_ext lib t t'
    -> {bterms' : list (@BTerm p)
        & computes_to_value_ext lib t' (oterm (Can op) bterms')
        # lblift (approx_ext_open lib) bterms bterms'}.
Proof.
  introv comp ap.
  invertsn ap.
  repnud ap.

  apply computes_to_value_implies_computes_to_val_exc in comp; eauto 3 with slow.

  apply ap2 in comp.
  exrepnd.

  apply clearbot_relbt in comp0.

  eexists; dands; eauto.
Qed.

Lemma computes_to_value_ext_eq {o} :
  forall lib (t v1 v2 : @NTerm o),
    t =e=v>(lib) v1
    -> t =e=v>(lib) v2
    -> v1 = v2.
Proof.
  introv comp1 comp2.
  eapply computes_to_value_eq;[apply comp1|apply comp2]; apply lib_extends_refl.
Qed.

Lemma cequiv_ext_canonical_form2 {pp} :
  forall lib t t' op bterms,
    computes_to_value lib t (oterm (Can op) bterms)
    -> cequiv_ext lib t t'
    -> {bterms' : list (@BTerm pp)
        & computes_to_value_ext lib t' (oterm (Can op) bterms')
        # cequiv_ext_bts lib bterms bterms'}.
Proof.
  introv comp ceq.
  allunfold @cequiv_ext; repnd.

  applydup @approx_ext_relates_only_progs in ceq; repnd.

  apply @approx_ext_canonical_form2 with (op := op) (bterms := bterms) in ceq0; auto; exrepnd.
  apply @approx_ext_canonical_form2 with (op := op) (bterms := bterms') in ceq; eauto 3 with slow; exrepnd.

  apply computes_to_value_implies_computes_to_val_exc in comp;[|eauto 3 with slow].

  eapply computes_to_value_ext_eq in ceq5;[|exact comp]; ginv.
  exists bterms'; sp.
  apply lblift_approx_ext_cequiv_ext; auto.
Qed.

Ltac prove_cequiv_ext_mk2 :=
  let Hcomp   := fresh "Hcomp" in
  let Hcomp1  := fresh "Hcomp1" in
  let Hcomp2  := fresh "Hcomp2" in
  let Hcomp3  := fresh "Hcomp3" in
  let Hcomp4  := fresh "Hcomp4" in
  let Hceq    := fresh "Hceq" in
  let bt      := fresh "bt" in
  let Hbt     := fresh "Hbt" in
  let bterms' := fresh "bterms'" in
  introv Hcomp Hceq;
    applydup @cequiv_ext_isprogram in Hceq; repnd;
    applydup @preserve_program in Hcomp as Hcomp1; auto;
    eapply @cequiv_ext_canonical_form2 in Hcomp; eauto;
    destruct Hcomp as [bterms' Hcomp];
    destruct Hcomp as [Hcomp2 Hcomp3];
    applydup @computes_to_value_ext_preserves_isprogram in Hcomp2 as Hcomp4; auto;
    unfold_all_mk;
    unfold_all_mk2;
    match goal with
      | [H : lblift _ _ ?bterms'  |- _ ] =>
        unfold lblift in H; simpl in H;
        let Hlen := fresh H "len" in
        destruct H as [Hlen H];   dlist_len_name bterms' bt
      | [H : cequiv_ext_bts _ _ ?bterms' |- _ ] =>
        unfold cequiv_ext_bts, lblift in H; simpl in H;
        let Hlen := fresh H "len" in
        destruct H as [Hlen H];   dlist_len_name bterms' bt
    end;
  dforall_lt_hyp Hbt;
  allunfold @selectbt; allsimpl;
  destruct_bterms;
  blift_nums;
  allunfold @num_bvars; allsimpl;
  dlists_len;
  unfold_all_mk;
  unfold_all_mk2;
  repeat(decomp_progh3);
  remove_relbt_samevar;
  foldlifts;
  rep_eexists; dands; eauto; apply @cequiv_ext_open_cequiv_ext;
     eauto 2 with slow.

Lemma cequiv_ext_mk_approx2 {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_approx a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p
        $ computes_to_value_ext lib t' (mk_approx a' b')
        # cequiv_ext lib a a'
        # cequiv_ext lib b b'}.
Proof.
  prove_cequiv_ext_mk2.
Qed.

Definition computes_to_valc_ext {o} (lib : @library o) (a b : @CTerm o) :=
  inExt lib (fun lib => computes_to_valc lib a b).

Lemma cequivc_ext_mkc_approx2 {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_approx a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p
        $ computes_to_valc_ext lib t' (mkc_approx a' b')
        # cequivc_ext lib a a'
        # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext.
  introv comp ceq; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_approx2 lib x2 x1 x0 x); intro k.
  repeat (autodimp k hyp); exrepnd.

  applydup @computes_to_value_ext_implies_computes_to_value in k0.
  applydup @computes_to_value_isvalue in k3 as j.
  inversion j as [u isp isc]; subst.
  allrw <- @isprogram_approx_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_cequiv {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_cequiv a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_cequiv a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk.
Qed.

(*
Lemma cequiv_extw_mkw_cequiv_ext :
  forall t t' a b,
    computes_to_valw t (mkw_cequiv_ext a b)
    -> cequiv_extw t t'
    -> {a', b' : WTerm &
         computes_to_valw t' (mkw_cequiv_ext a' b')
         # cequiv_extw a a'
         # cequiv_extw b b'}.
Proof.
  sp.
  destruct t, t', a, b.
  allunfold mkw_approx_ext.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_mk_cequiv_ext with (t' := x0) in H; sp.
  applydup cequiv_ext_wf_term in p1.
  applydup cequiv_ext_wf_term in p; sp.
  exists (existT wf_term a' p2) (existT wf_term b' p3).
  simpl; sp.
Qed.
*)

Lemma cequivc_ext_mkc_cequiv {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_cequiv a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_cequiv a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_cequiv lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_cequiv_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_sup {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_sup a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_sup a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_sup {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_sup a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_sup a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_sup lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_sup_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_refl {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_refl a)
    -> cequiv_ext lib t t'
    -> {a' : @NTerm p $
         computes_to_value lib t' (mk_refl a')
         # cequiv_ext lib a a'}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_refl {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_refl a)
    -> cequivc_ext lib t t'
    -> {a' : @CTerm p $
         computes_to_valc lib t' (mkc_refl a')
         # cequivc_ext lib a a'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_refl lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_refl_iff; repnd.
  exists (mk_cterm a' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_equality {p} :
  forall lib t t' a b T,
    computes_to_value lib t (mk_equality a b T)
    -> cequiv_ext lib t t'
    -> {a', b', T' : @NTerm p $
         computes_to_value lib t' (mk_equality a' b' T')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'
         # cequiv_ext lib T T'}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_equality {p} :
  forall lib t t' a b T,
    computes_to_valc lib t (mkc_equality a b T)
    -> cequivc_ext lib t t'
    -> {a', b', T' : @CTerm p $
         computes_to_valc lib t' (mkc_equality a' b' T')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'
         # cequivc_ext lib T T'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_equality lib x3 x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_equality_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp1) (mk_cterm T' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_requality {p} :
  forall lib t t' a b T,
    computes_to_value lib t (mk_requality a b T)
    -> cequiv_ext lib t t'
    -> {a', b', T' : @NTerm p $
         computes_to_value lib t' (mk_requality a' b' T')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'
         # cequiv_ext lib T T'}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_requality {p} :
  forall lib t t' a b T,
    computes_to_valc lib t (mkc_requality a b T)
    -> cequivc_ext lib t t'
    -> {a', b', T' : @CTerm p $
         computes_to_valc lib t' (mkc_requality a' b' T')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'
         # cequivc_ext lib T T'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_requality lib x3 x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_requality_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp1) (mk_cterm T' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_tequality {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_tequality a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_tequality a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_tequality {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_tequality a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_tequality a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_tequality lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_tequality_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_pertype {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_pertype a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_pertype b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_pertype {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_pertype a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_pertype b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_pertype lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_pertype_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_partial {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_partial a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_partial b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_partial {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_partial a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_partial b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_partial lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_partial_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_ipertype {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_ipertype a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_ipertype b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_ipertype {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_ipertype a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_ipertype b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_ipertype lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_ipertype_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_spertype {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_spertype a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_spertype b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_spertype {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_spertype a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_spertype b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_spertype lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_spertype_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_isect {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_isect A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_isect A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof.
  prove_cequiv_ext_mk.
Qed.

(*
Lemma cequiv_extw_mkw_isect :
  forall T T' A v B,
    computes_to_valw T (mkw_isect A v B)
    -> cequiv_extw T T'
    -> {A' : WTerm & {v' : NVar & {B' : WTerm &
         computes_to_valw T' (mkw_isect A' v' B')
         # cequiv_extw A A'
         # bcequiv_extw [v] B [v'] B'}}}.
Proof.
  sp.
  destruct T, T', A, B.
  allunfold mkw_isect.
  allunfold computes_to_valw.
  allsimpl.
  apply cequiv_ext_mk_isect with (T' := x0) in H; sp.
  applydup cequiv_ext_wf_term in p1; sp.
  applydup bcequiv_ext_wf_term in p; sp.

  exists (existT wf_term A' p2) v' (existT wf_term B' p4).
  simpl; sp.
Qed.
*)

Lemma cequivc_ext_mkc_isect {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_isect A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_isect A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_isect lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_isect_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_function {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_function A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_function A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_function {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_function A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_function A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_function lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_function_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_w {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_w A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_w A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequiv_ext_mk_pw {pp} :
  forall lib T T' P ap A bp ba B cp ca cb C p,
    computes_to_value lib T (mk_pw P ap A bp ba B cp ca cb C p)
    -> cequiv_ext lib T T'
    -> {P' : NTerm
        & {ap' : NVar
        & {A'  : NTerm
        & {bp' : NVar
        & {ba' : NVar
        & {B'  : NTerm
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C'  : NTerm
        & {p'  : @NTerm pp
           & computes_to_value lib T' (mk_pw P' ap' A' bp' ba' B' cp' ca' cb' C' p')
             # cequiv_ext lib P P'
             # bcequiv_ext lib (bterm [ap] A) (bterm [ap'] A')
             # bcequiv_ext lib (bterm [bp,ba] B) (bterm [bp',ba'] B')
             # bcequiv_ext lib (bterm [cp,ca,cb] C) (bterm [cp',ca',cb'] C')
             # cequiv_ext lib p p'
          }}}}}}}}}}}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_w {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_w A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_w A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_w lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_w_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_disect {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_disect A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_disect A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_disect {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_disect A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_disect A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_disect lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_disect_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

(* !!MOVE to list *)
Lemma no_repeats_singleton_iff :
  forall T (x : T), no_repeats [x] <=> True.
Proof.
  sp; split; sp.
Qed.

(**
Lemma bcequiv_ext_approx_extbt : forall bt1 bt2.
  bcequiv_ext lib bt1 bt2 <=> (approx_ext_open_bterm bt1 bt2 #  approx_ext_open_bterm bt1 bt2)
*)

Ltac simpl_list :=
  match goal with
    | [ H : context[length (map _ _)] |- _] => rewrite map_length in H
    | [ |-  context[length (map _ _)] ] => rewrite map_length
    | [ H : LIn ?x [?h] |- _ ] => apply in_single in H; subst
  end.

Lemma isprog_vars_isprogrambt {p} : forall nt lv,
  isprogram_bt (@bterm p lv nt) <=> isprog_vars lv nt.
Proof.
  introv.
  rw @isprog_vars_eq.
  unfold isprogram_bt. unfold closed_bt. simpl.
  rw <- null_iff_nil. rw null_remove_nvars_subvars.
  rw @bt_wf_iff.
  sp.
Qed.


Lemma bcequivc_ext1 {p} :
  forall lib v1 v2 t1 t2,
    @bcequivc_ext p lib [v1] t1 [v2] t2
    -> forall t,
         cequivc_ext lib (substc t v1 t1) (substc t v2 t2).
Proof.
  unfold bcequivc_ext ,cequivc_ext, get_cvterm, substc. introv Hbc. intro t.
  destruct_cterms; allsimpl.
  apply blift_cequiv_ext_approx_ext in Hbc. repnd.
  allrw @isprog_eq.
  allrw <- @isprog_vars_isprogrambt.
  apply approxbt_lsubst_prog with (lnt:=[x]) in Hbc; spcls;[| simpl_list; spcf].
  apply approxbt_lsubst_prog with (lnt:=[x]) in Hbc0; spcls;[| simpl_list; spcf].
  unfold subst. allsimpl.
  split; spc.
Qed.

(* !!MOVE to some computation file *)
Lemma can_doesnt_mark {p} :
  forall lib c bterms m, computes_to_marker lib (oterm (@Can p c) bterms) m -> False.
Proof.
  introv ce.
  destruct ce as [k r].
  apply reduces_to_if_isvalue_like in k; ginv; eauto 3 with slow.
Qed.

Lemma approx_ext_decomp_axiom0 {p} :
  forall lib a,
    @approx_ext p lib mk_axiom a <=> (isprogram a # computes_to_value lib a mk_axiom).
Proof.
  introv; split; intro k.

  - inversion k as [c]; subst.
    unfold close_compute_ext in c; repnd.
    generalize (c2 NAxiom []); intro h; repeat (autodimp h hyp).
    { apply computes_to_value_ext_isvalue_refl.
      apply isvalue_axiom. }
    exrepnd; dands; auto.
    inversion h0; allsimpl; cpx; eauto 3 with slow.

  - constructor; constructor; sp.

    + introv comp.
      apply computes_to_value_ext_isvalue_eq in comp; auto.
      unfold mk_axiom in *; ginv.
      exists ([] : list (@BTerm p)); dands; eauto 4 with slow.
      constructor; allsimpl; sp.

    + introv comp.
      apply computes_to_exception_ext_implies_computes_to_exception in comp.
      apply can_doesnt_raise_an_exception in comp; sp.

(*
    + introv comp.
      apply can_doesnt_mark in comp; sp.
*)

    + introv comp.
      apply computes_to_seq_ext_implies_computes_to_seq in comp.
      apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv.
Qed.

(*
(* !! MOVE to some computation file *)
Lemma computes_to_value_and_marker_false {p} :
  forall lib (a v : @NTerm p) m,
    computes_to_value lib a v
    -> computes_to_marker lib a m
    -> False.
Proof.
  introv cv ce.
  unfold computes_to_value in cv; repnd.
  unfold computes_to_marker in ce; repnd.
  apply reduces_to_or with (u := mk_marker m) in cv0; auto.
  destruct cv0 as [r|r].

  + apply reduces_to_marker in r; subst; sp.
    inversion cv.

  + apply reduces_to_if_value in r; subst; sp.
    inversion cv.
Qed.
*)

Lemma cequiv_ext_decomp_axiom0 {p} :
  forall lib a,
    @cequiv_ext p lib mk_axiom a <=> (isprogram a # computes_to_value lib a mk_axiom).
Proof.
  introv; split; intro k.

  - inversion k as [a1 a2].
    apply approx_ext_decomp_axiom0 in a1; sp.

  - constructor; repnd.
    apply approx_ext_decomp_axiom0; auto.
    constructor.
    split; dands; auto.

    + introv comp.
      apply computes_to_value_ext_implies_computes_to_value in comp.
      apply computes_to_value_eq with (v1 := mk_axiom) in comp; sp.
      unfold mk_axiom in *; ginv.
      exists ([] : list (@BTerm p)); fold_terms; dands; eauto 4 with slow.
      fold (@mk_axiom p).
      constructor; cpx.

    + introv comp.
      apply computes_to_exception_ext_implies_computes_to_exception in comp.
      apply computes_to_value_and_exception_false with (v := mk_axiom) in comp; sp.

(*
    + introv comp.
      apply computes_to_value_and_marker_false with (v := mk_axiom) in comp; sp.
*)

    + introv comp.
      apply computes_to_seq_ext_implies_computes_to_seq in comp.
      allunfold @computes_to_value; repnd.
      eapply reduces_to_eq_val_like in k1; try exact comp; eauto 3 with slow; ginv.
Qed.

Lemma approx_ext_decomp_axiom {p} :
  forall lib, @approx_ext p lib mk_axiom mk_axiom.
Proof.
  introv.
  generalize (@approx_ext_decomp_axiom0 p lib mk_axiom); sp.
  trewrite X; sp.
  apply computes_to_value_isvalue_refl.
  apply isvalue_axiom.
Qed.

Lemma cequiv_ext_decomp_axiom {p} :
  forall lib, @cequiv_ext p lib mk_axiom mk_axiom.
Proof.
  unfold cequiv_ext; sp; apply approx_ext_decomp_axiom.
Qed.

Lemma cequivc_ext_decomp_axiom {p} :
  forall lib, @cequivc_ext p lib mkc_axiom mkc_axiom.
Proof.
  unfold cequivc_ext; simpl; sp; apply cequiv_ext_decomp_axiom.
Qed.

(*
Lemma cequiv_ext_void :
  forall T T',
    computes_to_value lib T mk_void
    -> cequiv_ext lib T T'
    -> computes_to_value lib T' mk_void.
Proof.
  sp.
  apply cequiv_ext_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv_ext2 in p; sp; subst.
Qed.
*)

(*
Lemma cequiv_extw_void :
  forall T T',
    computes_to_valw T mkw_void
    -> cequiv_extw T T'
    -> computes_to_valw T' mkw_void.
Proof.
  sp.
  destruct T, T'.
  allunfold mkw_void.
  allunfold computes_to_val.
  allsimpl.
  apply cequiv_ext_void with (T := x); auto.
Qed.
*)

(*
Lemma cequivc_ext_void' :
  forall T T',
    computes_to_valuec T mk_void
    -> cequivc_ext lib T T'
    -> computes_to_valuec T' mk_void.
Proof.
  sp.
  apply cequivc_ext_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequivc_ext_void :
  forall T T',
    computes_to_valc lib T mkc_void
    -> cequivc_ext lib T T'
    -> computes_to_valc lib T' mkc_void.
Proof.
  sp.
  allapply computes_to_valc_to_valuec; allsimpl.
  apply cequivc_ext_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.
*)

(*
Lemma cequiv_exto_void :
  forall T T',
    computes_to_value lib T mk_void
    -> cequiv_exto T T'
    -> computes_to_value lib T' mk_void.
Proof.
  sp.
  apply cequiv_ext_canonical_form with (t' := T') in H; sp.
  apply lblift_cequiv_ext0 in H1; subst; auto.
Qed.
*)

(*
Lemma cequiv_extow_void :
  forall T T',
    computes_to_valw T mkw_void
    -> cequiv_extow T T'
    -> computes_to_valw T' mkw_void.
Proof.
  sp.
  destruct T, T'.
  allunfold mkw_void.
  allunfold computes_to_val.
  allsimpl.
  apply cequiv_ext_void with (T := x); auto.
Qed.
*)


Lemma approx_ext_decomp_cbv {p} :
  forall lib a1 v1 b1 a2 v2 b2,
    isprogram a1
    -> isprogram a2
    -> isprog_vars [v1] b1
    -> @isprog_vars p [v2] b2
    -> (approx_ext lib (mk_cbv a1 v1 b1) (mk_cbv a2 v2 b2)
        <=> forall t x,
              computes_to_value lib a1 x
              -> hasvalue lib (subst b1 v1 x)
              -> approx_ext lib a1 a2 # approx_ext lib (csubst b1 [(v1,t)]) (csubst b2 [(v2,t)])).
Proof.
  intros a1 v1 b1 a2 v2 b2 pa1 pa2 pb1 pb2; split; intro.

  inversion X; subst.
  inversion X0; repd.
  rw @isprogram_cbv_iff in X1; repd.
  rw @isprogram_cbv_iff in i; repd.
  intros.
Abort. (** this was Aborted before ; if needed, it should be provable*)

Lemma cequiv_ext_decomp_approx_ext {p} :
  forall lib a b c d,
    cequiv_ext lib (mk_approx a b) (@mk_approx p c d)
    <=> cequiv_ext lib a c # cequiv_ext lib b d.
Proof.
  intros.
  unfold cequiv_ext.
  generalize (approx_ext_decomp_approx_ext lib a b c d); intro.
  trewrite X; clear X.
  generalize (approx_ext_decomp_approx_ext lib c d a b); intro.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_ext_decomp_approx {p} :
  forall lib a b c d,
    cequivc_ext lib (mkc_approx a b) (@mkc_approx p c d)
    <=> cequivc_ext lib a c # cequivc_ext lib b d.
Proof.
  destruct a, b, c, d.
  unfold cequivc_ext, mkc_approx; simpl.
  apply cequiv_ext_decomp_approx_ext.
Qed.

Definition compute_to_approx_ext_exceptions {p} lib :=
  @close_compute_exc_ext p lib (approx_ext lib).
Definition compute_to_cequiv_ext_exceptions {p} lib (a b : @NTerm p) :=
  compute_to_approx_ext_exceptions lib a b # compute_to_approx_ext_exceptions lib b a.

Definition compute_to_approxc_ext_exceptions {p} lib (a b : @CTerm p) :=
  compute_to_approx_ext_exceptions lib (get_cterm a) (get_cterm b).
Definition compute_to_cequivc_ext_exceptions {p} lib (a b : @CTerm p) :=
  compute_to_cequiv_ext_exceptions lib (get_cterm a) (get_cterm b).

(*
(* !! MOVE to some computation file *)
Lemma if_computes_to_marker_cbv0 {p} :
  forall lib t v u e,
    isprogram t
    -> computes_to_marker lib (mk_cbv t v u) e
    -> {x : @NTerm p
        & computes_to_value lib t x
        # computes_to_marker lib (subst u v x) e}.
Proof.
  unfold computes_to_marker, reduces_to.
  introv ispt re; exrepnd.
  revert dependent t.
  revert v u e.
  induction k; introv ispt r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    simpl in r1.
    destruct t; try (complete (inversion r1)).
    dopid o as [can|ncan|exc|mrk|abs] Case; try (complete (inversion r1)).

    + Case "Can".
      inversion r1; subst; GC.
      unfold apply_bterm in r0; simpl in r0.
      rw @fold_subst in r0.
      exists (oterm (Can can) l); dands; sp.
      apply computes_to_value_can_same; sp.
      exists k; auto.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c.

      * inversion r1; subst; GC; allrw @fold_cbv.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in r0; auto; exrepnd.
        exists x; sp.
        apply computes_to_value_step with (t2 := n); auto.
        exists k0; auto.

      * inversion r1.

    + Case "Exc".
      unfold compute_step_catch in r1; inversion r1; subst; GC.
      apply reduces_in_atmost_k_steps_exception in r0; ginv.

    + Case "Mrk".
      allsimpl; ginv.
      unfold reduces_in_atmost_k_steps in r0.
      fold_terms; try (unfold mk_cbv in r0).
      rw @compute_at_most_k_steps_primarg_marker in r0; ginv.

    + Case "Abs".
      remember (compute_step lib (oterm (Abs abs) l)); destruct c.

      * inversion r1; subst; GC; allrw @fold_cbv.
        symmetry in Heqc.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in r0; auto; exrepnd.

        exists x; sp.
        apply computes_to_value_step with (t2 := n); auto.
        exists k0; auto.

      * inversion r1.
Qed.
*)

Lemma computes_to_seq_implies_computes_to_value {o} :
  forall lib (t : @NTerm o) f,
    isprogram t
    -> computes_to_seq lib t f
    -> computes_to_value lib t (sterm f).
Proof.
  introv isp comp.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Hint Resolve wf_cbv : slow.

Lemma approx_ext_decomp_halts_as_cbv {p} :
  forall lib a b,
    @isprogram p a
    -> isprogram b
    -> (approx_ext lib (mk_cbv a nvarx mk_axiom)
               (mk_cbv b nvarx mk_axiom)
        <=> ((hasvalue lib a -> hasvalue lib b)
             # compute_to_approx_ext_exceptions lib a b)).
Proof.
  introv pa pb; split; intro k.

  - dands.

    + intro hv.
      inversion k as [c].
      unfold close_compute_ext in c; repnd.
      allrw @isprogram_cbv_iff; repnd.
      unfold hasvalue in hv; exrepnd.
      apply cbv_reduce with (v := nvarx) (u := mk_axiom) in hv0;
        try (complete (rw @isprog_eq; sp)).
      rw @subst_mk_axiom in hv0.
      apply computes_to_value_if_reduces_to in hv0; auto.

      apply computes_to_value_implies_computes_to_val_exc in hv0;
        [|apply wf_cbv; eauto 3 with slow];[].

      applydup c2 in hv0; exrepnd.
      inversion hv2; allsimpl; cpx.

      apply computes_to_value_ext_implies_computes_to_value in hv1.

      apply computes_to_value_hasvalue in hv1.
      apply if_hasvalue_cbv0 in hv1; sp.
      rw @isprog_eq; auto.

    + introv ce.
      inversion k as [c].
      unfold close_compute_ext in c; repnd.

      apply computes_to_exception_ext_implies_computes_to_exception in ce.

      generalize (cbv_raises_exception lib a0 a nvarx mk_axiom e pa ce); intro h.

      apply computes_to_exception_implies_computes_to_exception_exc in h;[|eauto 3 with slow];[].

      apply c3 in h; exrepnd.

      apply computes_to_exception_ext_implies_computes_to_exception in h0.

      apply if_computes_to_exception_cbv0 in h0; auto.
      repndors; try (complete (inversion h1)); try (complete (inversion h2)).

      * exists a' e'; dands; tcsp; eauto 4 with slow.

      * exrepnd.
        rw @subst_mk_axiom in h3.
        apply can_doesnt_raise_an_exception in h3; sp.

  - constructor; constructor; sp;
    try (rw @isprogram_cbv_iff; sp; rw @nt_wf_eq; sp).

    + introv comp.

      apply computes_to_value_ext_implies_computes_to_value in comp.

      applydup @computes_to_value_hasvalue in comp.
      apply if_hasvalue_cbv0 in comp0; try (complete (rw @isprog_eq; sp)); sp.
      apply cbv_reduce0 with (v := nvarx) (u := mk_axiom) in comp0; sp;
      try (complete (rw @isprog_eq; sp)).
      apply cbv_reduce0 with (v := nvarx) (u := mk_axiom) in k0; sp;
      try (complete (rw @isprog_eq; sp)).
      apply computes_to_value_if_reduces_to in comp0; sp.
      apply computes_to_value_if_reduces_to in k0; sp.
      apply computes_to_value_eq with (v1 := mk_axiom) in comp; auto.
      unfold mk_axiom in *; ginv.
      exists ([] : list (@BTerm p)); fold (@mk_axiom p) in *; sp; eauto 3 with slow.
      { apply computes_to_value_implies_computes_to_val_exc; auto; apply wf_cbv; eauto 3 with slow. }
      constructor; simpl; sp.

    + introv comp.

      apply computes_to_exception_ext_implies_computes_to_exception in comp.

      apply if_computes_to_exception_cbv0 in comp; auto.
      repndors; exrepnd.

      * apply computes_to_exception_implies_computes_to_exception_exc in comp;[|eauto 3 with slow];[].

        apply k in comp; exrepnd.
        exists a' e'; dands; sp.

        apply computes_to_exception_implies_computes_to_exception_exc;[apply wf_cbv; eauto 3 with slow|].

        apply cbv_raises_exception; auto; eauto 3 with slow.

      * rw @subst_mk_axiom in comp0.
        apply can_doesnt_raise_an_exception in comp0; sp.

(*
    + introv comp.
      apply if_computes_to_marker_cbv0 in comp; auto; exrepnd.

      rw @subst_mk_axiom in comp0.
      apply can_doesnt_mark in comp0; sp.
*)

    + introv comp.

      apply computes_to_seq_ext_implies_computes_to_seq in comp.

      apply computes_to_seq_implies_computes_to_value in comp;
        try (apply isprogram_cbv_iff2; dands; auto;
             apply implies_isprogram_bt_lam;
             apply isprogram_lam;
             apply isprog_vars_axiom).
      applydup @computes_to_value_hasvalue in comp.
      apply if_hasvalue_cbv0 in comp0; try (complete (rw @isprog_eq; sp)); sp.
      apply cbv_reduce0 with (v := nvarx) (u := mk_axiom) in comp0; sp;
      try (complete (rw @isprog_eq; sp)).
      apply cbv_reduce0 with (v := nvarx) (u := mk_axiom) in k0; sp;
      try (complete (rw @isprog_eq; sp)).
      apply computes_to_value_if_reduces_to in comp0; sp.
      apply computes_to_value_if_reduces_to in k0; sp.
      apply computes_to_value_eq with (v1 := mk_axiom) in comp; auto.
      inversion comp; subst; allfold @mk_axiom.
Qed.

Lemma cequiv_ext_decomp_halts_as_cbv {p} :
  forall lib a b,
    @isprogram p a
    -> isprogram b
    -> (cequiv_ext lib (mk_cbv a nvarx mk_axiom)
               (mk_cbv b nvarx mk_axiom)
        <=> ((hasvalue lib a <=> hasvalue lib b)
             # compute_to_cequiv_ext_exceptions lib a b)).
Proof.
  unfold cequiv_ext; introv ispa ispb.
  generalize (approx_ext_decomp_halts_as_cbv lib a b ispa ispb); intro k.
  rw k; clear k.
  generalize (approx_ext_decomp_halts_as_cbv lib b a ispb ispa); intro k.
  rw k; clear k.
  unfold compute_to_cequiv_ext_exceptions.
  split; sp; discover; sp.
Qed.

Lemma cequivc_ext_decomp_halts_as_cbv {p} :
  forall lib a b,
    @cequivc_ext p lib (mkc_cbv a nvarx (mkcv_axiom nvarx))
            (mkc_cbv b nvarx (mkcv_axiom nvarx))
    <=> ((hasvaluec lib a <=> hasvaluec lib b)
         # compute_to_cequivc_ext_exceptions lib a b).
Proof.
  unfold cequivc_ext, hasvaluec; destruct a; destruct b; simpl.
  apply cequiv_ext_decomp_halts_as_cbv; allrw @isprogram_eq; sp.
Qed.

Lemma cequivc_ext_decomp_halts {p} :
  forall lib a b,
    @cequivc_ext p lib (mkc_halts a) (mkc_halts b)
    <=> ((hasvaluec lib a <=> hasvaluec lib b)
         # compute_to_cequivc_ext_exceptions lib a b).
Proof.
  intros; repeat (rewrite <- fold_mkc_halts).
  generalize (cequivc_ext_decomp_approx lib
                mkc_axiom
                (mkc_cbv a nvarx (mkcv_axiom nvarx))
                mkc_axiom
                (mkc_cbv b nvarx (mkcv_axiom nvarx))); sp.
  trewrite X; clear X.
  generalize (cequivc_ext_decomp_halts_as_cbv lib a b); sp.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma reduces_to_implies_cequiv_ext {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> cequiv_ext lib t x.
Proof.
  intros.
  apply reduces_to_implies_approx_ext in H; sp.
  constructor; sp.
Qed.

Lemma computes_to_value_implies_cequiv_ext {p} :
  forall lib t x,
    @isprogram p t
    -> computes_to_value lib t x
    -> cequiv_ext lib t x.
Proof.
  intros.
  apply computes_to_value_implies_approx_ext in X0; sp.
  constructor; sp.
Qed.

Lemma reduces_toc_implies_cequivc_ext {p} :
  forall lib t x,
    @reduces_toc p lib t x
    -> cequivc_ext lib t x.
Proof.
  destruct t; destruct x0; unfold reduces_toc, cequivc_ext; simpl.
  apply reduces_to_implies_cequiv_ext.
  rw @isprogram_eq; auto.
Qed.

Lemma computes_to_valc_implies_cequivc_ext {p} :
  forall lib t x,
    @computes_to_valc p lib t x
    -> cequivc_ext lib t x.
Proof.
  destruct t; destruct x0; unfold computes_to_valc, cequivc_ext; simpl.
  apply computes_to_value_implies_cequiv_ext.
  rw @isprogram_eq; auto.
Qed.

Lemma lblift_cequiv_ext_approx_ext {p} :
  forall lib (bterms1 bterms2 : list (@BTerm p)),
    cequiv_ext_bts lib bterms1 bterms2
    -> approx_ext_bts lib bterms1 bterms2
          # approx_ext_bts lib bterms2 bterms1.

Proof.
  unfoldlifts;
  induction bterms1; simpl; introv Hrc;
  destruct bterms2; allunfold @lblift; allsimpl; sp; try omega;
  dimp(Hrc n); auto; try omega; apply blift_cequiv_ext_approx_ext in hyp;
  repnd;
  destruct n; allsimpl; allunfold @selectbt; simpl;
   eauto; try omega.
Qed.

(* end hide *)
(** %\noindent% The following lemma
    is a straightforward consequence of
    the corresponding lemmas about [approx_ext].
    It is the holy grail of this section.

Since the type system that we define later will respect
[cequiv_ext] by definition, and [cequiv_ext] contains the computation relation,
we can easily prove, among other things, 
that reduction at any position inside of a term preserves its type.
*)

(*
    As a result, we will be able to prove that
    one can rewrite using [cequiv_ext]
    at any place in a Nuprl sequent.
    %\fixme{forward link to proof}%
*)

Lemma cequiv_ext_congruence {p} :
  forall lib o (lbt1 lbt2 : list (@BTerm p)),
    cequiv_ext_bts lib lbt1 lbt2
    -> isprogram (oterm o lbt1)
    -> isprogram (oterm o lbt2)
    -> cequiv_ext lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps H1p H2p.
   apply lblift_cequiv_ext_approx_ext in Haps. repnd.
   split; apply approx_ext_congruence; auto.
Qed.
(* begin hide *)

Lemma sp_implies_approx_ext_apply {p} :
  forall lib f g a,
    @isprogram p a
    -> approx_ext lib f g
    -> approx_ext lib (mk_apply f a) (mk_apply g a).
Proof.
  intros.
  apply implies_approx_ext_apply;sp.
  apply approx_ext_refl. sp.
Qed.


Lemma sp_implies_cequiv_ext_apply {p} :
  forall lib f g a,
    @isprogram p a
    -> cequiv_ext lib f g
    -> cequiv_ext lib (mk_apply f a) (mk_apply g a).
Proof.
  unfold cequiv_ext; sp; apply sp_implies_approx_ext_apply; sp.
Qed.

Lemma sp_implies_cequivc_ext_apply {p} :
  forall lib f g a,
    @cequivc_ext p lib f g
    -> cequivc_ext lib (mkc_apply f a) (mkc_apply g a).
Proof.
  destruct f, g, a; unfold cequivc_ext; simpl; sp.
  apply sp_implies_cequiv_ext_apply; sp.
  rw @isprogram_eq; sp.
Qed.

Lemma implies_cequivc_ext_apply {p} :
  forall lib f g a b,
    cequivc_ext lib f g
    -> @cequivc_ext p lib a b
    -> cequivc_ext lib (mkc_apply f a) (mkc_apply g b).
Proof.
  unfold cequivc_ext. introv H1c H2c.
  destruct_cterms. allsimpl. apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  repnd.
  split; apply implies_approx_ext_apply; auto.
Qed.

Lemma implies_cequivc_ext_apply2 {p} :
  forall lib f g a b c d,
    cequivc_ext lib f g
    -> cequivc_ext lib a c
    -> @cequivc_ext p lib b d
    -> cequivc_ext lib (mkc_apply2 f a b) (mkc_apply2 g c d).
Proof.
  introv c1 c2 c3.
  repeat (rw @mkc_apply2_eq).
  repeat (apply implies_cequivc_ext_apply); sp.
Qed.


Lemma alphaeqc_implies_cequivc_ext {p} :
  forall lib t1 t2,
    @alphaeqc p t1 t2
    -> cequivc_ext lib t1 t2.
Proof.
  introv aeq.
  allunfold @alphaeqc; allunfold @cequivc_ext.
  destruct_cterms; allsimpl.
  apply alpha_implies_cequiv_ext; sp; rw @isprogram_eq; sp.
Qed.

Lemma cequiv_ext_beta {p} :
  forall lib v b a,
    isprog_vars [v] b
    -> @isprogram p a
    -> cequiv_ext lib (mk_apply (mk_lam v b) a) (subst b v a).
Proof.
  introv ipb ipa.
  apply reduces_to_implies_cequiv_ext.
  apply isprogram_apply; sp.
  apply isprogram_lam; sp.

  unfold reduces_to.
  exists 1; simpl.
  unfold apply_bterm, subst; simpl; sp.
Qed.

Lemma cequivc_ext_beta {p} :
  forall lib v b a,
    cequivc_ext lib (mkc_apply (@mkc_lam p v b) a) (substc a v b).
Proof.
  introv.
  destruct_cterms; unfold cequivc_ext; simpl.
  apply cequiv_ext_beta; sp.
  allrw @isprogram_eq; sp.
Qed.

(* end hide *)
Inductive cequiv_ext_subst {p} (lib : @library p) : @Sub p -> @Sub p -> Type :=
  | ceq_sub_nil : cequiv_ext_subst lib [] []
  | ceq_sub_cons :
    forall v t1 t2 s1 s2,
      cequiv_ext lib t1 t2
      -> cequiv_ext_subst lib s1 s2
      -> cequiv_ext_subst lib ((v,t1) :: s1) ((v,t2) :: s2).
(* begin hide *)

Hint Constructors cequiv_ext_subst.

Lemma cequiv_ext_subst_snoc {p} :
  forall lib v t1 t2 s1 s2,
    cequiv_ext_subst lib s1 s2
    -> @cequiv_ext p lib t1 t2
    -> cequiv_ext_subst lib (snoc s1 (v,t1)) (snoc s2 (v,t2)).
Proof.
  induction s1; introv ceqsub ceq;
  inversion ceqsub; subst; simpl;
  apply ceq_sub_cons; sp.
Qed.

Lemma cequiv_ext_subst_csub2sub_refl {p} :
  forall lib s, cequiv_ext_subst lib (@csub2sub p s) (csub2sub s).
Proof.
  induction s; simpl; sp; simpl.
  apply ceq_sub_cons; sp.
  apply cequivc_ext_refl.
Qed.

Lemma cequiv_ext_subst_approx_ext {p} :
   forall lib suba subb,
   @cequiv_ext_subst p lib suba subb
   -> sub_range_rel (approx_ext lib) suba subb # sub_range_rel (approx_ext lib) subb suba.
Proof.
  induction suba as [| (va,ta) suba Hind]; introv Hl;
  destruct subb as [| (vb,tb) subb]; simpl; invertsna Hl Hll;
  auto;[]; apply Hind in Hll0; repnud Hll; repnd; dands; auto.
Qed.

Lemma lsubst_cequiv_ext_congr {p} : forall lib ta tb suba subb,
  @cequiv_ext_subst p lib suba subb
  -> cequiv_ext_open lib ta tb
  -> isprogram (lsubst ta suba)
  -> isprogram (lsubst tb subb)
  -> cequiv_ext lib (lsubst ta suba) (lsubst tb subb).
Proof.
  introv Hs Hoc H1p H2p.
  apply cequiv_ext_subst_approx_ext in Hs. repnd.
  apply olift_cequiv_ext_approx_ext in Hoc. repnd.
  split; apply lsubst_approx_ext_congr; auto.
Qed.


Lemma cequiv_ext_open_refl {p} :
  forall lib t,
    @nt_wf p t
    -> cequiv_ext_open lib t t.
Proof.
  introv Hnt. apply olift_approx_ext_cequiv_ext; apply approx_ext_open_refl; auto.
Qed.

(* end hide *)

(** %\noindent \\*% The following useful lemma is also
    a direct consequence of the corresponding property
    for [approx_ext].

*)


Lemma cequiv_ext_lsubst {p} :
  forall lib t sub1 sub2,
    isprogram (@lsubst p t sub1)
    -> isprogram (lsubst t sub2)
    -> cequiv_ext_subst lib sub1 sub2
    -> cequiv_ext lib (lsubst t sub1) (lsubst t sub2).
Proof.
  introv isp1 isp2 ceqsub.
  apply lsubst_cequiv_ext_congr; auto.
  apply cequiv_ext_open_refl.
  (* eauto with slow :*)
  eapply lsubst_nt_wf. 
  apply isprog_ntwf_eauto.
  exact isp2.
Qed.

(* begin hide *)

Definition lam_axiom {p} :=
  @mkc_lam p (cnewvar mkc_axiom) (mk_cv [cnewvar (@mkc_axiom p)] mkc_axiom).

Lemma cequivc_ext_app_lam_axiom {p} :
  forall lib a, @cequivc_ext p lib (mkc_apply lam_axiom a) mkc_axiom.
Proof.
  introv.
  unfold lam_axiom.
  generalize (cequivc_ext_beta lib
                (cnewvar mkc_axiom)
                (mk_cv [cnewvar (@mkc_axiom p)] mkc_axiom)
                a); intro ceq.
  rw @substc_cnewvar in ceq; auto.
Qed.

Lemma fold_cequivc_ext {p} :
  forall lib a b, cequiv_ext lib (get_cterm a) (@get_cterm p b) = cequivc_ext lib a b.
Proof. sp. Qed.

Lemma symm_rel_cequiv_ext_eauto {p} : forall lib, symm_rel (@cequiv_ext p lib).
Proof.
  introv Hs.
  eauto with slow.
Qed.
Hint Resolve symm_rel_cequiv_ext_eauto : respects.
Hint Resolve hasvalue_approx_ext : slow.

Lemma respects_cequiv_ext_hasval {p} :
  forall lib, respects1 (cequiv_ext lib) (@hasvalue p lib).
Proof.
  introv Hc Hsv.
  repnud Hc.
  eauto 2 with slow.
Qed.

Hint Resolve respects_cequiv_ext_hasval : respects.

Lemma respects_cequiv_ext_ceauiv_eauto {p} :
  forall lib, respects2 (cequiv_ext lib) (@cequiv_ext p lib).
Proof.
  split; introv Hc HH;
  eauto 3 with slow.
Qed.

Hint Resolve respects_cequiv_ext_ceauiv_eauto : respects.

Lemma alpha_implies_cequiv_ext_open {p} :
  forall lib (nt1 nt2 : @NTerm p),
  nt_wf nt1 -> nt_wf nt2 -> alpha_eq nt1 nt2 -> cequiv_ext_open lib nt1 nt2.
Proof.
  introv H1n H2n Hal.
  apply olift_approx_ext_cequiv_ext; eauto 
    with slow.
Qed.


Lemma hasvaluec_cequivc_ext {p} :
  forall lib t1 t2,
    @cequivc_ext p lib t1 t2
    -> hasvaluec lib t1
    -> hasvaluec lib t2.
Proof.
  introv Hcc Hv.
  allunfold @hasvaluec.
  allunfold @cequivc_ext.
  destruct_cterms.
  allsimpl.
  symmt Hcc.
  rwg Hcc.
  trivial.
Qed.


Lemma cequiv_ext_mk_inl {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_inl a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_inl b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.


Lemma cequivc_ext_mkc_inl {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_inl a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_inl b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_inl lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_inl_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_inr {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_inr a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_inr b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_inr {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_inr a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_inr b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_inr lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_inr_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

(* !!MOVE *)
Definition computes_to_excc {p} lib (a t1 t2 : @CTerm p) :=
  computes_to_exception lib (get_cterm a) (get_cterm t1) (get_cterm t2).

(* !!MOVE *)
Lemma computes_to_excc_eq {o} :
  forall lib (t : @CTerm o) a1 a2 v1 v2,
    computes_to_excc lib a1 t v1
    -> computes_to_excc lib a2 t v2
    -> a1 = a2 # v1 = v2.
Proof.
  introv comp1 comp2; destruct_cterms.
  allunfold @computes_to_excc; allsimpl.
  eapply reduces_to_exception_eq in comp1;[|exact comp2].
  apply computes_to_exception_exception in comp1; repnd; subst.
  eauto with pi.
Qed.

Lemma cequiv_ext_mk_texc {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_texc a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_texc a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk; allrw <- isprogram_texc_iff; sp.
Qed.

Lemma cequivc_ext_mkc_texc {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_texc a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_texc a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_texc lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_texc_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_union {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_union a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_union a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk; allrw <- isprogram_union_iff; sp.
Qed.

Lemma cequivc_ext_mkc_union {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_union a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_union a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_union lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_union_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_set {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_set A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_set A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof.
  prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_set {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_set A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_set A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_set lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_set_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_tunion {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_tunion A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_tunion A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof.
  prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_tunion {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_tunion A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_tunion A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_tunion lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_set_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_pair {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_pair a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_pair a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof.
  prove_cequiv_ext_mk; allrw <- isprogram_pair_iff; sp.
Qed.

Lemma cequivc_ext_mkc_pair {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_pair a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_pair a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_pair lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_pair_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_m {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_m A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_m A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_m {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_m A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_m A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_m lib x1 x0 x v x2); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_m_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_image {p} :
  forall lib t t' a b,
    computes_to_value lib t (mk_image a b)
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_image a' b')
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof. prove_cequiv_ext_mk; allrw <- isprogram_image_iff; sp.
Qed.

Lemma cequivc_ext_mkc_image {p} :
  forall lib t t' a b,
    computes_to_valc lib t (mkc_image a b)
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_valc lib t' (mkc_image a' b')
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_image lib x2 x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k0 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_image_iff; repnd.
  exists (mk_cterm a' isp0) (mk_cterm b' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_product {p} :
  forall lib T T' A v B,
    computes_to_value lib T (mk_product A v B)
    -> cequiv_ext lib T T'
    -> {A' : NTerm & {v' : NVar & {B' : @NTerm p &
         computes_to_value lib T' (mk_product A' v' B')
         # cequiv_ext lib A A'
         # bcequiv_ext lib (bterm [v] B) (bterm [v'] B')}}}.
Proof.
  prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_product {p} :
  forall lib T T' A v B,
    computes_to_valc lib T (mkc_product A v B)
    -> cequivc_ext lib T T'
    -> {A' : CTerm & {v' : NVar & {B' : @CVTerm p [v'] &
         computes_to_valc lib T' (mkc_product A' v' B')
         # cequivc_ext lib A A'
         # bcequivc_ext lib [v] B [v'] B'}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_product lib x1 x0 x v x2); intro k.
  repeat (autodimp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw <- @isprog_product_iff; repnd.
  exists (mk_ct A' isp0) v' (mk_cvterm [v'] B' isp); simpl; sp.
Qed.

Lemma cequiv_ext_mk_admiss {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_admiss a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_admiss b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequiv_ext_mk_mono {p} :
  forall lib t t' a,
    computes_to_value lib t (mk_mono a)
    -> cequiv_ext lib t t'
    -> {b : @NTerm p &
         computes_to_value lib t' (mk_mono b)
         # cequiv_ext lib a b}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequiv_ext_implies_cequiv_ext_open {p}:
  forall lib t1 t2,
    @cequiv_ext p lib t1 t2
    -> cequiv_ext_open lib t1 t2.
Proof.
  unfoldlifts.
  introv Hap.
  applydup @cequiv_ext_isprogram in Hap.
  repnd. unfold olift. dands; eauto 2 with slow.
  introv Hwf H1p H2p.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap1.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap0.
  rwg Hap0.
  rwg Hap1.
  trivial.
Qed.

Ltac prove_cequiv_ext :=
 unfold_all_mk;
 unfold_all_mk2;
  match goal with
    | [ |- cequiv_ext ?lib ?t ?t] => apply cequiv_ext_refl
    | [ |- (olift (cequiv_ext _)) ?t ?t] => apply cequiv_ext_open_refl
    | [ |- cequiv_ext_open _ ?t ?t] => apply cequiv_ext_open_refl
    | [ |- (olift (cequiv_ext _)) ?t1 ?t2] => apply cequiv_ext_implies_cequiv_ext_open
    | [ |- cequiv_ext_open _ ?t1 ?t2] => apply cequiv_ext_implies_cequiv_ext_open
    | [ |- cequiv_ext _ (oterm ?o _) (oterm ?o _)] => apply cequiv_ext_congruence
    | [ |- isprogram _] => repeat(decomp_progh); show_hyps; repeat(decomp_progc); sp
    | [ |- lblift (olift (cequiv_ext _)) _ _ ] =>
      (unfold lblift; simpl; dands;[spc|];
       let Hlt := fresh "XXHlt" in
       let n := fresh "XXn" in
       intros n Hlt;
       ( let rnum := (get_lt_rhs  Hlt)  in
         fail_if_not_number rnum; (*fail if not a normal form*)
         repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
      ))
    | [ |- cequiv_ext_bts _ _ _ ] =>
      (unfold cequiv_ext_bts, lblift; simpl; dands;[spc|];
       let Hlt := fresh "XXHlt" in
       let n := fresh "XXn" in
       intros n Hlt;
       ( let rnum := (get_lt_rhs  Hlt)  in
         fail_if_not_number rnum; (*fail if not a normal form*)
         repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
      ))
    | [ |- blift (olift (cequiv_ext _)) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    | [ |- blift (cequiv_ext_open _) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
end.


Lemma cequiv_ext_mkfix {p} : forall lib f fv,
  @cequiv_ext p lib f fv
  -> cequiv_ext lib (mk_fix f) (mk_fix fv).
Proof.
  allunfold @mk_fix. introv Hc.
  applydup @cequiv_ext_isprogram in Hc. repnd.
  repeat(prove_cequiv_ext); auto.
Qed.

Lemma cequivc_ext_mkcfix {p} : forall lib f fv,
  @cequivc_ext p lib f fv
  -> cequivc_ext lib (mkc_fix f) (mkc_fix fv).
Proof.
  allunfold @mk_fix. unfold cequivc_ext. introv Hc.
  dest_cterms Hc.
  allsimpl.
  allrw @isprog_eq.
  apply cequiv_ext_mkfix; auto.
Qed.



Lemma cequiv_ext_subst_congr {p} : forall lib f fv e v,
    @cequiv_ext p lib f fv
    -> isprogram (apply_bterm (bterm [v] e)  [f])
    -> cequiv_ext lib (lsubst e [(v, f)]) (lsubst e [(v, fv)]).
Proof.
  introv Hred Hpr.
  applydup @cequiv_ext_isprogram in Hred. repnd.
  rename Hred into Hc.
  eapply (ceq_sub_cons _ v _ _  [] []) in Hc; auto.
  allunfold @apply_bterm.
  allsimpl. duplicate Hpr as Hprf.
  apply prog_sub_change with (sub2:=[(v, fv)]) in Hpr; auto;
    try (prove_sub_range_sat; eauto 2 with slow);[].
  apply cequiv_ext_lsubst with (t:=e) in Hc; auto.
Qed.



Lemma cequivc_ext_mkc_admiss {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_admiss a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_admiss b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_admiss lib x1 x0 x); intro k.
  repeat (autodimp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_admiss_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma cequivc_ext_mkc_mono {p} :
  forall lib t t' a,
    computes_to_valc lib t (mkc_mono a)
    -> cequivc_ext lib t t'
    -> {b : @CTerm p &
         computes_to_valc lib t' (mkc_mono b)
         # cequivc_ext lib a b}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_mono lib x1 x0 x); intro k.
  repeat (autodimp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_mono_iff; repnd.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma subst_cequiv_ext {p} :
  forall lib t a b x,
    isprogram a
    -> @isprogram p b
    -> isprog_vars [x] t
    -> cequiv_ext lib a b
    -> cequiv_ext lib (subst t x a) (subst t x b).
Proof.
  introv ipa ipb ipt c.
  unfold subst.
  apply cequiv_ext_lsubst;
    try (apply @isprogram_lsubst; simpl; sp; cpx;
         allrw @isprog_vars_eq; allrw subvars_prop; discover; sp).
  constructor; sp.
Qed.

Lemma substc_cequivc_ext {p} :
  forall lib a b x t,
    @cequivc_ext p lib a b
    -> cequivc_ext lib (substc a x t) (substc b x t).
Proof.
  introv c.
  destruct_cterms; allunfold @cequivc_ext; allsimpl.
  apply subst_cequiv_ext; sp; allrw @isprogram_eq; sp.
Qed.
Hint Resolve substc_cequivc_ext : cequivc_ext.

Lemma cequivc_ext_apply_id {p} :
  forall lib t, @cequivc_ext p lib (mkc_apply mkc_id t) t.
Proof.
  introv.
  apply reduces_toc_implies_cequivc_ext; auto.
Qed.
Hint Immediate cequivc_ext_apply_id.

Lemma implies_approx_ext_ispair {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    @approx_ext p lib a1 a2
    -> approx_ext lib b1 b2
    -> approx_ext lib c1 c2
    -> approx_ext lib (mk_ispair a1 b1 c1) (mk_ispair a2 b2 c2).
Proof.
  introv apa apb apc.
  applydup @approx_ext_relates_only_progs in apa.
  applydup @approx_ext_relates_only_progs in apb.
  applydup @approx_ext_relates_only_progs in apc.
  repnd.
  unfold mk_ispair, mk_can_test.
  repeat prove_approx_ext; sp.
Qed.

Lemma implies_cequivc_ext_ispair {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    cequivc_ext lib a1 a2
    -> cequivc_ext lib b1 b2
    -> @cequivc_ext p lib c1 c2
    -> cequivc_ext lib (mkc_ispair a1 b1 c1) (mkc_ispair a2 b2 c2).
Proof.
  unfold cequivc_ext.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  repnud ceqc.
  split; apply implies_approx_ext_ispair; auto.
Qed.

Lemma cequivc_ext_mkc_pw {pp} :
  forall lib T T' P ap A bp ba B cp ca cb C p,
    computes_to_valc lib T (mkc_pw P ap A bp ba B cp ca cb C p)
    -> cequivc_ext lib T T'
    -> {P' : CTerm
        & {ap' : NVar
        & {A' : CVTerm [ap']
        & {bp' : NVar
        & {ba' : NVar
        & {B' : CVTerm [bp',ba']
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C' : CVTerm [cp',ca',cb']
        & {p' : @CTerm pp
           & computes_to_valc lib T' (mkc_pw P' ap' A' bp' ba' B' cp' ca' cb' C' p')
           # cequivc_ext lib P P'
           # bcequivc_ext lib [ap] A [ap'] A'
           # bcequivc_ext lib [bp,ba] B [bp',ba'] B'
           # bcequivc_ext lib [cp,ca,cb] C [cp',ca',cb'] C'
           # cequivc_ext lib p p'
          }}}}}}}}}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_pw lib x2 x1 x0 ap x5 bp ba x4 cp ca cb x3 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw @fold_pw.
  apply isprog_pw_iff in isp; repnd.
  exists (mk_ct P' isp0)
         ap' (mk_cvterm [ap'] A' isp1)
         bp' ba' (mk_cvterm [bp',ba'] B' isp2).
  exists cp' ca' cb' (mk_cvterm [cp',ca',cb'] C' isp3)
         (mk_ct p' isp);
    simpl; sp.
Qed.

Lemma cequiv_ext_mk_pm {pp} :
  forall lib T T' P ap A bp ba B cp ca cb C p,
    computes_to_value lib T (mk_pm P ap A bp ba B cp ca cb C p)
    -> cequiv_ext lib T T'
    -> {P' : NTerm
        & {ap' : NVar
        & {A'  : NTerm
        & {bp' : NVar
        & {ba' : NVar
        & {B'  : NTerm
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C'  : NTerm
        & {p'  : @NTerm pp
           & computes_to_value lib T' (mk_pm P' ap' A' bp' ba' B' cp' ca' cb' C' p')
             # cequiv_ext lib P P'
             # bcequiv_ext lib (bterm [ap] A) (bterm [ap'] A')
             # bcequiv_ext lib (bterm [bp,ba] B) (bterm [bp',ba'] B')
             # bcequiv_ext lib (bterm [cp,ca,cb] C) (bterm [cp',ca',cb'] C')
             # cequiv_ext lib p p'
          }}}}}}}}}}}.
Proof. prove_cequiv_ext_mk.
Qed.

Lemma cequivc_ext_mkc_pm {pp} :
  forall lib T T' P ap A bp ba B cp ca cb C p,
    computes_to_valc lib T (mkc_pm P ap A bp ba B cp ca cb C p)
    -> cequivc_ext lib T T'
    -> {P' : CTerm
        & {ap' : NVar
        & {A' : CVTerm [ap']
        & {bp' : NVar
        & {ba' : NVar
        & {B' : CVTerm [bp',ba']
        & {cp' : NVar
        & {ca' : NVar
        & {cb' : NVar
        & {C' : CVTerm [cp',ca',cb']
        & {p' : @CTerm pp
           & computes_to_valc lib T' (mkc_pm P' ap' A' bp' ba' B' cp' ca' cb' C' p')
           # cequivc_ext lib P P'
           # bcequivc_ext lib [ap] A [ap'] A'
           # bcequivc_ext lib [bp,ba] B [bp',ba'] B'
           # bcequivc_ext lib [cp,ca,cb] C [cp',ca',cb'] C'
           # cequivc_ext lib p p'
          }}}}}}}}}}}.
Proof.
  unfold computes_to_valc, cequivc_ext; intros; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_pm lib x2 x1 x0 ap x5 bp ba x4 cp ca cb x3 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp w]; subst.
  allrw @isprogram_eq.
  allrw @fold_pm.
  apply isprog_pm_iff in isp; repnd.
  exists (mk_ct P' isp0)
         ap' (mk_cvterm [ap'] A' isp1)
         bp' ba' (mk_cvterm [bp',ba'] B' isp2).
  exists cp' ca' cb' (mk_cvterm [cp',ca',cb'] C' isp3)
         (mk_ct p' isp);
    simpl; sp.
Qed.

Lemma cequiv_ext_mk_exception {p} :
  forall lib t t' a b,
    computes_to_exception lib a t b
    -> cequiv_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_exception lib a' t' b'
         # cequiv_ext lib a a'
         # cequiv_ext lib b b'}.
Proof.
  introv Hcomp Hceq.
  allunfold @cequiv_ext; repnd.
  applydup @approx_ext_relates_only_progs in Hceq; repnd.
  applydup @reduces_to_implies_approx_ext1 in Hcomp; auto.

  eapply approx_ext_trans in Hceq0;[|exact Hcomp0].
  apply approx_ext_exception in Hceq0; exrepnd.

  applydup @reduces_to_implies_approx_ext1 in Hceq3; auto.
  eapply approx_ext_trans in Hceq;[|exact Hceq5].
  apply approx_ext_exception in Hceq; exrepnd.

  eapply reduces_to_exception_eq in Hcomp;[|exact Hceq6].
  apply computes_to_exception_exception in Hcomp; repnd; subst.

  exists x c; dands; auto.
Qed.

Lemma cequivc_ext_mkc_exception {p} :
  forall lib t t' a b,
    computes_to_excc lib a t b
    -> cequivc_ext lib t t'
    -> {a', b' : @CTerm p $
         computes_to_excc lib a' t' b'
         # cequivc_ext lib a a'
         # cequivc_ext lib b b'}.
Proof.
  unfold computes_to_excc, cequivc_ext; introv comp ceq; destruct_cterms; allsimpl.
  generalize (cequiv_ext_mk_exception lib x2 x1 x0 x); intro k.
  repeat (autodimp k hyp); exrepnd.
  applydup @cequiv_ext_isprog in k2 as ispa.
  applydup @cequiv_ext_isprog in k1 as ispb.
  repnd.
  exists (mk_ct a' ispa) (mk_ct b' ispb); simpl.
  dands; auto.
Qed.

Lemma cequiv_ext_uatom {pp} :
  forall lib T T',
    @computes_to_value pp lib T mk_uatom
    -> cequiv_ext lib T T'
    -> computes_to_value lib T' mk_uatom.
Proof.
  sp.
  apply cequiv_ext_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequivc_ext_uatom {pp} :
  forall lib T T',
    computes_to_valc lib T mkc_uatom
    -> @cequivc_ext pp lib T T'
    -> computes_to_valc lib T' mkc_uatom.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_ext_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequiv_ext_utoken {pp} :
  forall lib T T' u,
    @computes_to_value pp lib T (mk_utoken u)
    -> cequiv_ext lib T T'
    -> computes_to_value lib T' (mk_utoken u).
Proof.
  sp.
  apply cequiv_ext_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv_ext0 in p; subst; auto.
Qed.

Lemma cequivc_ext_utoken {pp} :
  forall lib T T' u,
    computes_to_valc lib T (mkc_utoken u)
    -> @cequivc_ext pp lib T T'
    -> computes_to_valc lib T' (mkc_utoken u).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_ext_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv_ext0 in p; subst; auto.
Qed.

(* end hide *)
(**
Later, we will show that one can rewrite by [cequiv_ext] at any place in a hypothesis
([rule_cequiv_ext_subst_hyp] in Sec. %\ref{sec:rules:cequiv_ext}%)
or the conclusion
([rule_cequiv_ext_subst_concl] in Sec. %\ref{sec:rules:cequiv_ext}%)
in a Nuprl proof.
*)

(* do not put any code below this. Place it above the begin hide *)
