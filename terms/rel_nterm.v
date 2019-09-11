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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export bin_rels.
Require Export alphaeq.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #<=># *)
(** printing [+]  $+$ #[+]# *)
(** printing <  $<$ #<# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)
(** printing {[  $[$ #[# *)
(** printing ]}  $]$ #]# *)

Notation "tls {[ m ]}" := (selectbt tls m)
  (at level 99).

(** When we define the type system in the next chapter, we will
    want it to respect many computational relations.
    In Agda, Coq and Nuprl, if [t] reduces to [t'],
    and [t] is in some type [T], then [t]
    and [t'] are equal in [T].
    In addition, it is useful to have our types respect a
    %\emph{congruence}% that contains the computation relation.  For
    example, Coq has a notion of definitional equality which is a
    congruence.  In Nuprl, we have a computation equivalence
    $\sim$ %\cite{Howe:1989}%, which is a coinductively
    defined congruence that permits more powerful equational reasoning.
    For example, all diverging programs are equivalent under
    $\sim$.  The same holds for all programs that
    generate an infinite stream of zeroes.

    Following him, we will first define his computational approximation
    ([approx]) and prove that it is a congruence.
    The desired equivalence([cequiv]) is defined as a conjuction of
    [approx] with its inverse. In the next chapter, 
    our definition of Nuprl's type system
    will respect [cequiv] by definition.
    We often denote [cequiv] by $\sim$.
    
    We will also prove many domain theoretic properties about [approx] in the
    next section. These properties will be useful in defining partial types.
 *)

 
(** We begin by describing some key definitions involved in the defining
    of [approx]. Firstly, [olift] lifts a binary relation that is
    meaningful only on programs to
    to one on well-formed([nt_wf]) terms that
    may have free variables. Recall
    that a program is a well-formed term that is also closed.
    the [wf_sub] predicate on [Substitution] asserts that the range of
    the substitution consists of well-formed terms.
    (One could have used the [CTerm] type to make
    this definition more compact.)
    Intuitively,  [(olift R) s t] asserts
    that for all substitutions that turn [s] and [t]
    to closed terms [s'] and [t'], [R s' t'] holds.
*)

Definition NTrel {o} := @NTerm o -> @NTerm o -> [univ].


Definition olift {p} (R : NTrel) (x y : NTerm) : [univ] :=
  nt_wf x # nt_wf y
  # forall sub: @Substitution p,
      wf_sub sub
      -> isprogram (lsubst x sub)
      -> isprogram (lsubst y sub)
      -> R (lsubst x sub) (lsubst y sub).

(**

  We show later that oliftp and olift are equivalent if R respects
  alpha equivalence.

*)
Definition oliftp {p} (R : NTrel) (x y :NTerm) : [univ] :=
  nt_wf x # nt_wf y
  # forall sub: @CSub p,
      cover_vars x sub
      -> cover_vars y sub
      -> R (csubst x sub) (csubst y sub).



(** % \noindent \\* % [blift] and [lblift]
    lift a binary relation on [NTerm]s to one on [BTerm]s and one on
    lists of [BTerm] respectively.
   *)

Definition blift {p} (R: NTrel) (bt1 bt2: BTerm): [univ] :=
{lv: (list NVar) &  {nt1,nt2 : @NTerm p $ R nt1 nt2
  # alpha_eq_bterm bt1 (bterm lv nt1) # alpha_eq_bterm bt2 (bterm lv nt2) }}.

Definition lblift {p} (R: NTrel)
                      (tls trs: list (@BTerm p)): [univ] :=
length tls = length trs 
# forall n : nat,  n < length tls -> blift R (tls{[n]}) (trs{[n]}).

(** %\fxnote{coqdoc notation messed up above : ]\}}% *)
(* begin hide *)
Definition blift_old {p} (R : NTerm -> NTerm -> Type) (a b : BTerm) : Type :=
  num_bvars a = num_bvars b
  # forall lnt : list (@NTerm p),
       (**approx_refl proof required the next 2 lines*)
       length lnt = num_bvars a
       -> (forall nt : NTerm, LIn nt lnt -> isprogram nt)
       -> R (apply_bterm a lnt) (apply_bterm b lnt).


Definition is_rel_on_progs {p} (R: bin_rel (@NTerm p)) : Type :=
  forall t1 t2, R t1 t2 -> isprogram t1 # isprogram t2.

Theorem le_blift {p} :
  forall (R1 R2 : bin_rel (@NTerm p)),
    le_bin_rel R1 R2 -> le_bin_rel (blift  R1) (blift R2).
Proof.
  unfold le_bin_rel.
  intros R1 R2 Hle a b Hrel.
  allunfold @blift. sp.
  exists lv nt1 nt2.
  split; eauto.
Defined.

Theorem le_olift {p} :
  forall (R1 R2 : bin_rel (@NTerm p)),
    le_bin_rel R1 R2 -> le_bin_rel (olift  R1) (olift R2).
Proof.
  unfold le_bin_rel, olift. sp.
Defined.

Hint Resolve @le_olift : slow.


Theorem le_blift2 {p} : forall (R1 R2 : bin_rel (@NTerm p)),
  (le_bin_rel R1 R2) -> forall a b, (blift  R1  a b) -> (blift R2  a b).
Proof. intros R1 R2 n H.
  fold (@le_bin_rel (BTerm ) (blift R1 ) (blift R2 )).
 apply le_blift. auto.
Defined.

Hint Resolve le_blift2 : slow.



Theorem le_lblift {p} : forall (R1 R2 : bin_rel (@NTerm p)),
  (le_bin_rel R1 R2) -> le_bin_rel (lblift  R1) (lblift  R2).
Proof.
  unfold lblift; sp.
  unfold le_bin_rel; sp.
  generalize (X0 n); sp.
  apply @le_blift2 with (R1 := R1); sp.
Defined.


Theorem le_lblift2 {p} : forall (R1 R2 : bin_rel (@NTerm p)),
  (le_bin_rel R1 R2) -> forall a b, (lblift R1 a b) -> (lblift  R2 a b).
Proof. intros R1 R2 H.
  fold (@le_bin_rel (list BTerm) (lblift R1 ) (lblift R2 )).
 apply le_lblift. auto.
Defined.

(*
Inductive toProp (T: Type): Prop :=
trunc : T -> toProp T.
*)


Theorem eq_blift_olift {p} :
  forall (R1 R2 : bin_rel (@NTerm p)),
    eq_bin_rel R1 R2 -> eq_bin_rel (olift  R1) (olift R2).
Proof.
  unfold eq_bin_rel. split; repnd; eauto with slow.
Qed.

Lemma blift_refl {p} :
  forall (R : bin_rel (@NTerm p)),
    refl_rel R
    -> refl_rel (blift R).
Proof.
  unfold refl_rel, blift; sp.
  destruct x as [lv nt].
  exists lv nt nt.
  eauto with slow.
Qed.

(* end hide *)
(** Below, we define some abstractions to denote that
  a relation respects another relation. In particular,
  we are interested in proving that many relations
  respect alpha equaliity *)

Definition respects2_l {T1 T2 : tuniv}
           (Rr : T1 -> T1 -> [univ])
           (R  : T1 -> T2 -> [univ]) :=
  forall a b a', Rr a a' -> R a b -> R a' b.

Definition respects2_r {T1 T2 : tuniv}
           (Rr : T2 -> T2 -> [univ])
           (R  : T1 -> T2 -> [univ]) :=
  forall a b b', Rr b b' -> R a b -> R a b'.


Definition respects2 {T : tuniv}
           (Rr : T -> T -> [univ])
           (R : T -> T -> [univ]):=
  (respects2_l Rr R) # (respects2_r Rr R).


Notation respects_alpha := (respects2 alpha_eq).



Lemma olift_iff_oliftp {p} :
  forall R a b,
    respects_alpha R
    -> (@olift p R a b <=> oliftp R a b).
Proof.
  introv resp; unfold olift, oliftp; split; intro o; repnd; dands; auto.

  - introv cva cvb.
    generalize (o (csub2sub sub)); intro k.
    repeat (autodimp k hyp).

    + apply isprogram_lsubst; auto.

      * introv i; apply in_csub2sub in i; auto.

      * introv i.
        rw @cover_vars_eq in cva.
        rw subvars_prop in cva.
        apply cva in i.
        rw @dom_csub_eq; auto.

    + apply isprogram_lsubst; auto.

      * introv i; apply in_csub2sub in i; auto.

      * introv i.
        rw @cover_vars_eq in cvb.
        rw subvars_prop in cvb.
        apply cvb in i.
        rw @dom_csub_eq; auto.

  - introv wfsub ispa ispb.
    generalize (lsubst_trim2_alpha1 a b sub ispa ispb); intro k.
    remember (sub_keep_first sub (free_vars a ++ free_vars b)).
    simpl in k; repnd.
    generalize (lsubst_trim2_alpha2 a b sub wfsub ispa ispb); intro ps.
    rw <- Heqs in ps.
    generalize (prog_sub_exists_csub s ps); intro e; exrepnd.
    assert (dom_csub s0 = dom_sub s) as domeq by (rw <- e0; rw @dom_csub_eq; auto).

    assert (cover_vars a s0) as ca.
    rw @cover_vars_eq.
    rw subvars_prop; introv i.
    rw domeq.
    rw Heqs.
    apply lsubst_program_implies in ispa.
    applydup ispa in i.
    applydup @in_dom_sub_exists in i0; exrepnd.
    apply @in_dom_sub with (t := t).
    apply in_sub_keep_first; dands; auto.
    rw in_app_iff; auto.

    assert (cover_vars b s0) as cb.
    rw @cover_vars_eq.
    rw subvars_prop; introv i.
    rw domeq.
    rw Heqs.
    apply lsubst_program_implies in ispb.
    applydup ispb in i.
    applydup @in_dom_sub_exists in i0; exrepnd.
    apply @in_dom_sub with (t := t).
    apply in_sub_keep_first; dands; auto.
    rw in_app_iff; auto.

    generalize (o s0 ca cb); intro r.
    unfold csubst in r.
    rw e0 in r.

    destruct resp as [rl rr].
    applydup @alpha_eq_sym in k0.
    applydup @alpha_eq_sym in k.
    generalize (rl (lsubst a s) (lsubst b sub) (lsubst a sub) k1);
      intro j1; repeat (autodimp j1 hyp).
    generalize (rr (lsubst a s) (lsubst b s) (lsubst b sub) k2);
      intro j2; repeat (autodimp j2 hyp).
Qed.


(* begin hide *)


Notation  respects_alpha_l :=  (@respects2_l NTerm NTerm alpha_eq).
Notation  respects_alpha_r :=  (@respects2_r NTerm NTerm alpha_eq).

Definition respects1 {T : tuniv} (Rr : T -> T -> [univ])  
                                 (R : T  -> [univ]):=
     forall a a', Rr a a' -> R a -> R a'.

Definition respects3_l {TL TM TR : tuniv} (Rr : TL -> TL -> [univ]) 
                                      (R : TL -> TM -> TR -> [univ]):=
     forall a b c a' , Rr a a' -> R a b c -> R a' b c.

Definition respects3_m {TL TM TR : tuniv} (Rr : TM -> TM -> [univ]) 
                                      (R : TL -> TM -> TR -> [univ]):=
     forall a b c b', Rr b b' -> R a b c -> R a b' c.

Definition respects3_r {TL TM TR : tuniv} (Rr : TR -> TR -> [univ]) 
                                      (R : TL -> TM -> TR -> [univ]):=
     forall a b c c', Rr c c' -> R a b c -> R a b c'.

Definition respects3 {T : tuniv} (Rr : T -> T -> [univ])  
                                 (R : T -> T -> T -> [univ]):=
     (respects3_l Rr R) # (respects3_m Rr R) # (respects3_r Rr R).


Lemma respects2_l_eauto : forall {T: tuniv} Rr (R : T-> T-> [univ]),
  respects2 Rr R -> (respects2_l Rr R).
Proof.
  intros. repnud X.
  auto.
Qed.

Lemma respects2_r_eauto : forall {T: tuniv} Rr (R : T-> T-> [univ]),
  respects2 Rr R -> (respects2_r Rr R).
Proof.
  intros. repnud X.
  auto.
Qed.

Hint Resolve respects2_l_eauto  respects2_r_eauto : respects.

Ltac rwhg  Hal H := let xrr := fresh "XRR" in 
match type of Hal with
| ?Rr ?la ?ra =>
  match type of H with
  | ?R la => assert (respects1 Rr R) as xrr by eauto with respects;
      apply (xrr _ _ Hal) in H;clear xrr

  | ?R la _ => assert (respects2_l Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ Hal) in H;clear xrr
  | ?R _ la => assert (respects2_r Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ Hal) in H;clear xrr

  | ?R la _ _ => assert (respects3_l Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ _ Hal) in H;clear xrr
  | ?R _ la _ => assert (respects3_m Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ _ Hal) in H;clear xrr
  | ?R _ _ la => assert (respects3_r Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ _ Hal) in H;clear xrr
  end
end.

Lemma sym_alpha_eauto {p} : symm_rel (@alpha_eq p).
Proof.
  introv Hab.
  eauto with slow.
Qed.

Hint Resolve  sym_alpha_eauto: respects.

Ltac rwg  Hal := let xrr := fresh "XRR" in 
                let Xsym := fresh "Xsym" in 
match type of Hal with
| ?Rr ?la ?ra => assert (symm_rel Rr) as Xsym;
  [eauto with respects;
    idtac ":add symmetry of this relation to the database"; fail|];
  match goal with
  | [ |- ?R la ] => assert (respects1 Rr R) as xrr by (eauto with respects;
       idtac "missing hint:1");
      apply (xrr _ _  (Xsym _ _ Hal));clear xrr

  | [ |- ?R la _ ] => assert (respects2_l Rr R) as xrr by (eauto with respects;
       idtac "missing hint:2_l");
      apply (xrr _ _ _ (Xsym _ _ Hal));clear xrr
  | [ |- ?R _ la ]  => assert (respects2_r Rr R) as xrr by (eauto with respects;
       idtac "missing hint:2_r");
      apply (xrr _ _ _ (Xsym _ _ Hal));clear xrr

  | [ |- ?R la _ _] => assert (respects3_l Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ _ (Xsym _ _ Hal));clear xrr
  | [ |- ?R _ la _]  => assert (respects3_m Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ _ (Xsym _ _ Hal));clear xrr
  | [ |- ?R _ _ la ]  => assert (respects3_r Rr R) as xrr by eauto with respects;
      apply (xrr _ _ _ _ (Xsym _ _ Hal));clear xrr

  end; clear Xsym
end.

Lemma respects3_l_eauto : forall {T: tuniv} Rr (R : T-> T -> T -> [univ]),
  respects3 Rr R -> (respects3_l Rr R).
Proof.
  intros. repnud X.
  auto.
Qed.

Lemma respects3_m_eauto : forall {T: tuniv} Rr (R : T->  T -> T-> [univ]),
  respects3 Rr R -> (respects3_m Rr R).
Proof.
  intros. repnud X.
  auto.
Qed.

Lemma respects3_r_eauto : forall {T: tuniv} Rr (R : T-> T -> T -> [univ]),
  respects3 Rr R -> (respects3_r Rr R).
Proof.
  intros. repnud X.
  auto.
Qed.


Hint Resolve respects3_l_eauto respects3_m_eauto respects3_r_eauto : respects.



Ltac symmt Hal :=
  let Xsym := fresh "Xsym" in
  match type of Hal with
    | ?Rr ?la ?ra =>
      assert (symm_rel Rr) as Xsym;
        [ eauto with respects;
          idtac ":add symmetry of this relation to the database";
          fail
        | apply Xsym in Hal;
          clear Xsym
        ]
  end.

Ltac rwgs Hal := (rwg Hal || (symmt Hal; rwg Hal) ).

Theorem olift_relates_only_wf {p} : forall R t1 t2, (@olift p R) t1 t2
  -> nt_wf t1 # nt_wf t2.
Proof. introv H. repnud H. split; auto.
Qed.

Theorem olift_vars_lsubst {p} :
  forall R a b lvi lvo, let sub := @var_ren p lvi lvo in 
   (respects_alpha R)
   ->  (olift R) a b
   -> (olift R) (lsubst a sub) (lsubst b sub).
Proof.
  introv Hra Hap.
  applydup @olift_relates_only_wf in Hap.
  pose proof (@wf_sub_vars p lvi lvo) as Hwf.
  repeat(split; [apply lsubst_wf_iff;sp;fail|]).
  introv Hwfs H1ps H2pr.
  repnud Hap.
  pose proof (@allvars_combine p lvi lvo) as Hss.
  pose proof (combine_1var_sub_wspec (var_ren lvi lvo) sub) as Hsub. 
  repeat(dest_imp Hsub HH).
  exrepnd.
  pose proof (Hsub0 a) as Hala. alpha_hyps Hala.
  pose proof (Hsub0 b) as Halb. alpha_hyps Halb.
  pose proof (Hap sub3) as XX.
  repeat(dest_imp XX HH).
  rwg Hala.
  rwg Halb.
  trivial.
Qed.

Lemma respects_alpha_olift_l {p} : forall R,
  respects_alpha_l R
  -> respects_alpha_l (@olift p R).
Proof.
  introv Hra.  introv Hal Hap.
  repnud Hap.
  alpha_hyps Hal.
  unfold olift. dands; spcf.
  introv Hwf Hla' Hlb.
  dimp (Hap sub); spc; eauto 3 with slow.
  apply @lsubst_alpha_congr2 with (sub:=sub)in Hal.
  apply alphaeq_preserves_program in Hal.
  destruct Hal; auto.
Qed.

Lemma respects_alpha_olift_r {p} : forall R,
  respects_alpha_r R
  -> respects_alpha_r (@olift p R).
Proof.
  introv Hra.  introv Hal Hap.
  repnud Hap.
  alpha_hyps Hal.
  unfold olift. dands; spcf.
  introv Hwf Hla' Hlb.
  dimp (Hap sub); spc; eauto 3 with slow.
  apply @lsubst_alpha_congr2 with (sub:=sub)in Hal.
  apply alphaeq_preserves_program in Hal.
  destruct Hal; auto.
Qed.

(* end hide *)
Lemma respects_alpha_olift {p}: forall R,
  respects2 alpha_eq R
  -> respects2 alpha_eq (@olift p R).
Proof.
  introv Hr. repnud Hr.
  split.
  - apply respects_alpha_olift_l;  trivial.
  - apply respects_alpha_olift_r; trivial.
Qed.
(* begin hide *)

Hint Resolve respects_alpha_olift : respects.


Lemma blift_oliftd {p} : forall R bt1 bt2 lva,
  (respects_alpha R)
  -> blift (olift R) bt1 bt2
  -> {lvn : (list NVar) & {nt1',nt2' : @NTerm p $ (olift R) nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # no_repeats lvn
          (* # disjoint lvn (all_vars (get_nt bt1) ++ all_vars (get_nt bt2)) *)
          # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lva   } }.
Proof.
  introv Hra Hab.
  repnud Hab. exrepnd.
  pose proof (alpha_bterm_pair_change _ _ _ _ _ lva Hab2 Hab0) as Hp.
  exrepnd.
  exists lvn.
  rwhg Hp2 Hab1.
  rwhg Hp3 Hab1.
  exists (lsubst nt1n (var_ren lv lvn)).
  exists (lsubst nt2n (var_ren lv lvn)).
  spc;[| disjoint_reasoningv;spcls;
        apply disjoint_bound_vars_lsubst; spcls;disjoint_reasoningv;fail].
  apply olift_vars_lsubst;spc.
Qed.


  
Lemma blift_selen_triv {p} : forall R lv a b,
  (respects_alpha R)
  -> blift (olift R )(bterm lv a) (@bterm p lv b)
  -> (olift R) a b.
Proof.
  introv Hra Has.
  apply (blift_oliftd R _ _ lv) in Has; auto.
  exrepnd.
  pose proof (change_bvars_alpha_wspec lv a) as Hfa.
  exrepnd. rename ntcv into a'.
  rwg Hfa0.
  apply @alpha_eq_bterm_congr with (lv:=lv) in Hfa0.
  assert (alpha_eq_bterm (bterm lv a') (bterm lvn nt1')) 
      as Xa by eauto with slow.

  pose proof (change_bvars_alpha_wspec lv b) as Hfb.
  exrepnd. rename ntcv into b'.
  rwg Hfb0.
  apply @alpha_eq_bterm_congr with (lv:=lv) in Hfb0.
  assert (alpha_eq_bterm (bterm lv b') (bterm lvn nt2')) 
      as Xb by eauto with slow.
  clear dependent a.
  clear dependent b.
  invertsna Xa Hb.
  invertsna Xb Ha.
  apply lsubst_alpha_congr2 with (sub:=var_ren lv3 lv) in Ha3.
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  apply lsubst_alpha_congr2 with (sub:=var_ren lv0 lv) in Hb3.
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  Hint Resolve lsubst_trivial_alpha : slow.
  assert (alpha_eq b' (lsubst nt2' (var_ren lvn lv))) as Xa by eauto with slow.
  assert (alpha_eq a' (lsubst nt1' (var_ren lvn lv))) as Xb by eauto with slow.
  clear Ha3 Hb3.
  apply olift_vars_lsubst with (lvi:=lvn) (lvo:=lv) in Has1;spc;[].
  rwg Xa.
  rwg Xb.
  auto.
Qed.

Lemma le_blift_olift {p} :
  forall R1 R2 : bin_rel (@NTerm p),
  le_bin_rel R1 R2 -> le_bin_rel (blift (olift R1)) 
      (blift (olift R2)).
Proof.
  introv Ha.
  apply le_blift.
  apply le_olift; auto.
Qed.



Lemma blift_alpha_fun_r {p} :
  forall R nt1 nt2 nt2',
  @blift p R nt1 nt2
  -> alpha_eq_bterm nt2 nt2'
  -> blift R nt1 nt2'.
Proof.
  introv Has Hal.
  repnud Has .
  exrepnd.
  unfold blift.
  exists lv nt0 nt3.
  dands; eauto with slow.
Qed.

Lemma blift_alpha_fun_l {p} :
  forall R nt1 nt1' nt2,
  @blift p R nt1 nt2
  -> alpha_eq_bterm nt1 nt1'
  -> blift R nt1' nt2.
Proof.
  introv Has Hal.
  repnud Has .
  exrepnd.
  unfold blift.
  exists lv nt0 nt3.
  dands; eauto with slow.
Qed.

(* end hide *)
(** %\noindent% Because of the way alpha equality
    is baked into the definition of [blift],
    for any binary relation [R] on [NTerm],
    [blift R] respects alpha equality of bound terms.
*)

Lemma respects_blift_alphabt {p} : forall (R : bin_rel (@NTerm p)),
  respects2 alpha_eq_bterm (blift R).
Proof.
  intros Hr.
  split; introv Hyp;
  eauto using blift_alpha_fun_l, blift_alpha_fun_r.
Qed.

(** %\noindent% We will use the following lemmas later
    in this document.

*)
Lemma blift_numbvars {p} : forall R bt1 bt2,
  @blift p R bt1 bt2
  -> num_bvars bt1= num_bvars bt2.
Proof.
  introv Hr.
  repnud Hr.
  exrepnd.
  inverts Hr0.
  inverts Hr2.
  unfold num_bvars. simpl. spc.
Qed.
(* begin hide *) 





Ltac blift_nums :=
repeat match goal with
[H : blift _ (bterm _ _) (bterm _ _) |- _ ] => 
  let Hnum := fresh H "num" in
  pose proof (blift_numbvars _ _ _ H) as Hnum; hide_hyp H
end; show_hyps.

Ltac remove_relbt_samevar := 
repeat match goal with
[H : blift _ (bterm ?lv _) (bterm ?lv _) |- _ ] =>
  let Hnorel := fresh H "norel" in
  pose proof H as Hnorel;
  apply blift_selen_triv in Hnorel; eauto with respects; hide_hyp H;
  try(idtac; [| idtac "hint missing"])
end; show_hyps.

Lemma symmrel_alpha_eq_bterm_eauto {p} : symm_rel (@alpha_eq_bterm p).
Proof.
  introv Hb.
  eauto with slow.
Qed.

Hint Resolve symmrel_alpha_eq_bterm_eauto : respects.

Lemma respect_eauto_albt {p} : respects1 alpha_eq_bterm (@bt_wf p).
Proof.
  introv. introns XX.
  apply (alphaeqbt_preserves_wf _ _ XX) in XX0.
  auto.
Qed.

Lemma symm_rel_eauto_99 {p} : symm_rel (@alpha_eq_bterm p).
Proof.
  introv ; eauto with slow.
Qed.

Hint Resolve respect_eauto_albt symm_rel_eauto_99 : respects.

Lemma alphabt_blift {p} : forall R,
(le_bin_rel ( fun x y => @alpha_eq p x y # nt_wf x # nt_wf y) R)
-> (le_bin_rel ( fun x y => alpha_eq_bterm x y # bt_wf x # bt_wf y) (blift R)).
Proof.
  introv Hle Hal. allsimpl.
  unfolds_base. repnd.
  applydup @alpha_eq_bterm_unify in Hal0.
  exrepnd.
  exists lv nta ntb.
  dands; auto. apply Hle.
  assert (alpha_eq_bterm (bterm lv nta) (bterm lv ntb)) as Hnal by 
    eauto using alpha_eq_bterm_trans, alpha_eq_bterm_sym.
  rwhg Hal3 Hal.
  rwhg Hal2 Hal1.
  invertsn Hal.
  invertsn Hal1.
  dands; auto.
  apply alpha_eq_bterm_triv in Hnal.
  auto.
Qed.

(*
Lemma lblift_refl :
  forall R,
    rel_rel NTerm R
    -> rel_rel (list BTerm) (lblift R).
Proof.
  sp; unfold rel_rel; sp.
  constructor; sp.
  apply blift_refl in X.
  unfold rel_rel in X; sp.
Qed.

Lemma blift_refl_p :
  forall R : NTerm -> NTerm -> Type,
    (forall t, isprogram t -> R t t)
    -> forall bt, isprogram_bt bt -> blift R bt bt.
Proof.
  sp; constructor; sp.
  apply X.
  unfold apply_bterm; destruct bt; allsimpl.
  inversion X0.
  inversion X2; subst.
  apply isprogram_lsubst; sp.
  allapply in_combine; sp.
  inversion H0.
  rw <- null_iff_nil in H2.
  rw null_remove_nvars in H2.
  apply_in_hyp p.
  apply implies_in_combine; sp.
Qed.

Lemma lblift_refl_p :
  forall R : NTerm -> NTerm -> Type,
    (forall t, isprogram t -> R t t)
    -> forall l, (forall bt, LIn bt l -> isprogram_bt bt) -> lblift R l l.
Proof.
  sp; constructor; sp.
  apply blift_refl_p; sp.
  apply X0.
  apply selectbt_in; sp.
Qed.
*)