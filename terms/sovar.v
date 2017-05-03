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


Require Export alphaeq.
Require Export swap.
Require Export tactics2.
Require Export terms_apply.


(**

  Similar to [NTerm]s but here variables can be second order variables.

 *)
Inductive SOTerm {o} : tuniv :=
| sovar : NVar -> list SOTerm -> SOTerm
| soseq : (nat -> @NTerm o) -> SOTerm
| soterm : @Opid o -> list SOBTerm -> SOTerm
with SOBTerm {o} : tuniv :=
| sobterm : list NVar -> SOTerm -> SOBTerm.


Definition mk_soaxiom {o} : @SOTerm o := soterm (Can NAxiom) [].


(*
(**

  true if the [SOTerm] is a [NTerm]

 *)
Fixpoint is_nterm {o} (t : @SOTerm o) : bool :=
  match t with
    | sovar _ [] => true
    | sovar _ _ => false
    | soterm _ bs => ball (map is_bterm bs)
  end
with is_bterm {o} (bt : @SOBTerm o) : bool :=
       match bt with
         | sobterm _ t => is_nterm t
       end.
*)

(**

  Converts a [SOTerm] into a [NTerm] by turning second order variables
  into applications of first order variables.

 *)
Fixpoint soterm2nterm {o} (t : @SOTerm o) : @NTerm o :=
  match t with
  | sovar v ts => apply_list (mk_var v) (map soterm2nterm ts)
  | soseq s => sterm s
  | soterm opid bs => oterm opid (map sobterm2bterm bs)
  end
with sobterm2bterm {o} (bt : @SOBTerm o) : @BTerm o :=
       match bt with
         | sobterm vs t => bterm vs (soterm2nterm t)
       end.

Fixpoint nterm2soterm {o} (t : @NTerm o) : @SOTerm o :=
  match t with
  | vterm v => sovar v []
  | sterm s => soseq s
  | oterm opid bs => soterm opid (map bterm2sobterm bs)
  end
with bterm2sobterm {o} (bt : @BTerm o) : @SOBTerm o :=
       match bt with
       | bterm vs t => sobterm vs (nterm2soterm t)
       end.

Definition sovar_sig := NVar # nat.

Ltac dsovar_sig :=
  match goal with
    | [ H : sovar_sig |- _ ] => destruct H
  end.

Ltac dsovar_sigs := repeat dsovar_sig.

Lemma sovar_sig_dec: forall x y : sovar_sig, {x = y} + {x <> y}.
Proof.
  intros.
  dsovar_sigs.
  destruct (deq_nvar n n1); subst; tcsp;
    destruct (eq_nat_dec n0 n2); subst; tcsp;
      right; sp; cpx.
Defined.

Definition memsovar (v : sovar_sig) vs : LIn v vs + !LIn v vs.
Proof.
  exact (in_deq sovar_sig sovar_sig_dec v vs).
Qed.

Definition subsovars (vs1 vs2 : list sovar_sig) :=
  assert (subsetb sovar_sig_dec vs1 vs2).

Lemma subsovars_proof_irrelevance :
  forall vs1 vs2,
  forall x y : subsovars vs1 vs2,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : subsovars ?vs1 ?vs2 , H2 : subsovars ?vs1 ?vs2 |- _ ] =>
    pose proof (subsovars_proof_irrelevance vs1 vs2 H2 H1) as h; subst
end : pi.

Lemma subsovars_eq :
  forall vs1 vs2,
    subsovars vs1 vs2 <=> subset vs1 vs2.
Proof.
  sp; unfold subsovars.
  trw assert_subsetb; sp.
Qed.

Lemma subsovars_refl :
  forall vs,
    subsovars vs vs.
Proof.
  sp.
  rw subsovars_eq.
  apply subset_refl.
Qed.
Hint Immediate subsovars_refl.

Lemma subsovars_prop :
  forall vs1 vs2,
    subsovars vs1 vs2 <=> forall x, LIn x vs1 -> LIn x vs2.
Proof.
  sp; rw subsovars_eq; unfold subset; split; sp.
Qed.

Lemma subsovars_trans :
  forall vs1 vs2 vs3,
    subsovars vs1 vs2
    -> subsovars vs2 vs3
    -> subsovars vs1 vs3.
Proof.
  introv h1 h2.
  allrw subsovars_eq.
  eapply subset_trans; eauto.
Qed.

Lemma subsovars_nil_l :
  forall vs, subsovars [] vs.
Proof.
  introv; apply subsovars_prop; allsimpl; sp.
Qed.
Hint Immediate subsovars_nil_l.

Lemma subsovars_cons_lr :
  forall v vs1 vs2,
    subsovars vs1 vs2
    -> subsovars (v :: vs1) (v :: vs2).
Proof.
  introv sv.
  allrw subsovars_prop; introv i; allsimpl; sp.
Qed.

Lemma subsovars_cons_weak_r :
  forall v vs1 vs2,
    subsovars vs1 vs2
    -> subsovars vs1 (v :: vs2).
Proof.
  introv sv.
  allrw subsovars_prop; introv i; allsimpl; sp.
Qed.

Definition remove_so_vars (vs1 vs2 : list sovar_sig) := diff sovar_sig_dec vs1 vs2.

Lemma remove_so_vars_cons_r :
  forall l v vars,
    remove_so_vars l (v :: vars)
    = if memsovar v l then remove_so_vars l vars
      else v :: remove_so_vars l vars.
Proof.
  intros; unfold remove_so_vars.
  boolvar; rewrite diff_cons_r; boolvar; sp.
Qed.

Definition var2sovar (v : NVar) : sovar_sig := (v,0).

Definition sovar2var (l : sovar_sig) : NVar := fst l.

Definition sovars2vars := map sovar2var.

Definition vars2sovars := map var2sovar.

Fixpoint so_free_vars {o} (t : @SOTerm o) : list sovar_sig :=
  match t with
  | sovar v ts => (v,length ts) :: (flat_map so_free_vars ts)
  | soseq s => []
  | soterm op bs => flat_map so_free_vars_bterm bs
  end
with so_free_vars_bterm {o} (bt : @SOBTerm o) : list sovar_sig :=
       match bt with
         | sobterm vs t =>
           remove_so_vars
             (vars2sovars vs)
             (so_free_vars t)
       end.

Fixpoint all_fo_vars {o} (t : @SOTerm o) : list NVar :=
  match t with
  | sovar v ts => v :: flat_map all_fo_vars ts
  | soseq s => []
  | soterm op bs => flat_map all_fo_vars_bterm bs
  end
with all_fo_vars_bterm {o} (bt : @SOBTerm o) : list NVar :=
       match bt with
         | sobterm vs t => vs ++ all_fo_vars t
       end.

Fixpoint fo_bound_vars {p} (t : @SOTerm p) : list NVar :=
  match t with
  | sovar _ ts => flat_map fo_bound_vars ts
  | soseq _ => []
  | soterm op bs => flat_map fo_bound_vars_bterm bs
  end
with fo_bound_vars_bterm {p} (bt : @SOBTerm p) : list NVar :=
       match bt with
         | sobterm lv nt => lv ++ fo_bound_vars nt
       end.

Definition so_bound_vars {o} (t : @SOTerm o) : list sovar_sig :=
  vars2sovars (fo_bound_vars t).

Definition wf_soterm {p} (t : @SOTerm p) := wf_term (soterm2nterm t).

Definition wf_sobterm {p} (bt : @SOBTerm p) := wf_bterm (sobterm2bterm bt).

Lemma wf_soterm_proof_irrelevance {p} :
  forall t : @SOTerm p,
  forall x y : wf_soterm t,
    x = y.
Proof.
  intros.
  apply UIP.
Qed.
Hint Immediate wf_soterm_proof_irrelevance.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_soterm ?t , H2 : wf_soterm ?t |- _ ] =>
    pose proof (wf_soterm_proof_irrelevance t H2 H1) as h; subst
end : pi.

Inductive sosub_kind {o} :=
| sosk : list NVar -> @NTerm o -> sosub_kind.

Definition allvars_sk {o} (sk : @sosub_kind o) : list NVar :=
  match sk with
    | sosk vs t => vs ++ allvars t
  end.

Definition sosk_vs {o} (sk : @sosub_kind o) : list NVar :=
  match sk with
    | sosk vs _ => vs
  end.

Definition sosk_t {o} (sk : @sosub_kind o) : NTerm :=
  match sk with
    | sosk _ t => t
  end.

Definition bterm2sk {o} (bt : @BTerm o) : sosub_kind :=
  match bt with
    | bterm vs t => sosk vs t
  end.

Definition sk2bterm {o} (sk : @sosub_kind o) : BTerm :=
  match sk with
    | sosk vs t => bterm vs t
  end.

Definition SOSub {o} := list (NVar # @sosub_kind o).

Definition sodom {o} (s : @SOSub o) : list sovar_sig :=
  map (fun x =>
         match x with
           | (v, sosk vs t) => (v, length vs)
         end)
      s.

Definition sorange {o} (s : @SOSub o) : list BTerm :=
  map (fun x =>
         match x with
           | (v, sosk vs t) => bterm vs t
         end)
      s.

Lemma in_sorange {o} :
  forall (sub : @SOSub o) bt,
    LIn bt (sorange sub) <=> {v : NVar & LIn (v,bterm2sk bt) sub}.
Proof.
  introv.
  rw in_map_iff; split; intro k; exrepnd; subst.
  - destruct a; simpl; eexists; eauto.
  - destruct bt; allsimpl; eexists; eauto.
Qed.

Fixpoint sosub_filter {p} (sub : @SOSub p) (vars : list sovar_sig) : SOSub :=
  match sub with
    | nil => nil
    | (v, (sosk vs t) as k) :: xs =>
      if memsovar (v,length vs) vars
      then sosub_filter xs vars
      else (v, k) :: sosub_filter xs vars
  end.

Fixpoint sosub_find {p} (sub : @SOSub p) (sv : sovar_sig) : option sosub_kind :=
  match sub with
    | nil => None
    | (v, (sosk vs t) as k) :: xs =>
      if sovar_sig_dec sv (v,length vs)
      then Some k
      else sosub_find xs sv
  end.

(*
Fixpoint lift_list_option {T} (l : list (option T)) : option (list T) :=
  match l with
    | [] => Some []
    | Some x :: rest =>
      match lift_list_option rest with
        | Some xs => Some (x :: xs)
        | None => None
      end
    | None :: rest => None
  end.
*)

(* For the lsubst_aux to work, we will require the bound_vars of sub to
 * be disjoint from all the vars of t *)
Fixpoint sosub_aux {o} (sub : @SOSub o) (t : SOTerm) : NTerm :=
  match t with
  | sovar var ts =>
    match sosub_find sub (var,length ts) with
    | Some (sosk vs u) => lsubst_aux u (combine vs (map (sosub_aux sub) ts))
    | None => apply_list (mk_var var) (map (sosub_aux sub) ts)
    end
  | soseq s => sterm s
  | soterm opid bts => oterm opid (map (sosub_b_aux sub) bts)
  end
with sosub_b_aux {o} (sub : @SOSub o) (bt : SOBTerm) : BTerm :=
       match bt with
       | sobterm vs t =>
         bterm vs (sosub_aux (sosub_filter sub (vars2sovars vs)) t)
       end.

Definition free_vars_sk {o} (sk : @sosub_kind o) : list NVar :=
  match sk with
    | sosk vs t => remove_nvars vs (free_vars t)
  end.

(* Same as free_vars_sk *)
Definition free_vars_sosub_kind {o} (sk : @sosub_kind o) :=
  free_vars_bterm (sk2bterm sk).

Lemma free_vars_sk_is_free_vars_sosub_kind {o} :
  forall sk : @sosub_kind o,
    free_vars_sk sk = free_vars_sosub_kind sk.
Proof.
  destruct sk.
  unfold free_vars_sk, free_vars_sosub_kind; simpl; auto.
Qed.

Definition free_vars_sosub {o} (sub : @SOSub o) : list NVar :=
  flat_map (fun x => free_vars_sk (snd x)) sub.

Definition bound_vars_in_sk {o} (sk : @sosub_kind o) : list NVar :=
  match sk with
    | sosk _ t => bound_vars t
  end.

Definition bound_vars_in_sosub {o} (sub : @SOSub o) : list NVar :=
  flat_map (fun x => bound_vars_in_sk (snd x)) sub.

Definition bound_vars_sk {o} (sk : @sosub_kind o) : list NVar :=
  match sk with
    | sosk vs t => vs ++ bound_vars t
  end.

Definition bound_vars_sosub {o} (sub : @SOSub o) : list NVar :=
  flat_map (fun x => bound_vars_sk (snd x)) sub.

Definition foren := list (NVar # NVar).

Definition soren := list (sovar_sig # NVar).

Definition foren_dom (ren : foren) : list NVar := map (fun v => fst v) ren.
Definition soren_dom (ren : soren) : list sovar_sig := map (fun v => fst v) ren.

Lemma foren_dom_app :
  forall ren1 ren2,
    foren_dom (ren1 ++ ren2) = foren_dom ren1 ++ foren_dom ren2.
Proof.
  introv; unfold foren_dom; rw map_app; auto.
Qed.

Definition mk_foren (vs1 vs2 : list NVar) : foren := combine vs1 vs2.
Definition mk_soren (vs1 : list sovar_sig) (vs2 : list NVar) : soren :=
  combine vs1 vs2.

Lemma foren_dom_mk_foren :
  forall vs1 vs2, length vs1 = length vs2 -> foren_dom (mk_foren vs1 vs2) = vs1.
Proof.
  induction vs1; introv e; allsimpl; auto.
  destruct vs2; allsimpl; cpx.
  rw IHvs1; auto.
Qed.

Lemma soren_dom_mk_soren :
  forall vs1 vs2, length vs1 = length vs2 -> soren_dom (mk_soren vs1 vs2) = vs1.
Proof.
  induction vs1; introv e; allsimpl; auto.
  destruct vs2; allsimpl; cpx.
  rw IHvs1; auto.
Qed.

Definition foren2soren (ren : foren) : soren :=
  map (fun x =>
         match x with
           | (v1,v2) => (var2sovar v1, v2)
         end)
      ren.

Lemma foren2soren_app :
  forall ren1 ren2,
    foren2soren (ren1 ++ ren2) = foren2soren ren1 ++ foren2soren ren2.
Proof.
  induction ren1; simpl; auto.
  destruct a; introv.
  rw IHren1; auto.
Qed.

Fixpoint foren_vars (ren : foren) : list NVar :=
  match ren with
    | nil => nil
    | (v1,v2) :: xs => v1 :: v2 :: foren_vars xs
  end.

Fixpoint soren_vars (ren : soren) : list NVar :=
  match ren with
    | nil => nil
    | ((v1,n),v2) :: xs => v1 :: v2 :: soren_vars xs
  end.

Fixpoint foren_filter (ren : foren) (vars : list NVar) : foren :=
  match ren with
    | nil => nil
    | (v1, v2) :: xs =>
      if memvar v1 vars
      then foren_filter xs vars
      else (v1,v2) :: foren_filter xs vars
  end.

Fixpoint foren_find (ren : foren) (v : NVar) : option NVar :=
  match ren with
    | nil => None
    | (v1, v2) :: xs =>
      if deq_nvar v1 v
      then Some v2
      else foren_find xs v
  end.

Fixpoint soren_find (ren : soren) (v : sovar_sig) : option sovar_sig :=
  match ren with
    | nil => None
    | ((v1,n) as sv, v2) :: xs =>
      if sovar_sig_dec sv v
      then Some (v2,n)
      else soren_find xs v
  end.

Definition rename_var (ren : foren) (v : NVar) : NVar :=
  match foren_find ren v with
    | Some w => w
    | None => v
  end.

Definition rename_sovar (ren : soren) (v : sovar_sig) : sovar_sig :=
  match soren_find ren v with
    | Some w => w
    | None => v
  end.

Lemma rename_var_cons :
  forall v1 v2 ren v,
    rename_var ((v1,v2) :: ren) v
    = if deq_nvar v1 v
      then v2
      else rename_var ren v.
Proof.
  introv; unfold rename_var; simpl; boolvar; auto.
Qed.

Lemma rename_sovar_nil :
  forall v, rename_sovar [] v = v.
Proof. sp. Qed.

Lemma rename_sovar_cons :
  forall v1 n v2 ren v,
    rename_sovar (((v1,n),v2) :: ren) v
    = if sovar_sig_dec (v1,n) v
      then (v2,n)
      else rename_sovar ren v.
Proof.
  introv; unfold rename_sovar; simpl; boolvar; auto.
Qed.

Fixpoint fo_change_bvars_alpha {p} (disj : list NVar) (ren : foren) (t : @SOTerm p) :=
  match t with
  | sovar v ts =>
    if bnull ts
    then sovar (rename_var ren v) []
    else sovar v (map (fo_change_bvars_alpha disj ren) ts)
  | soseq s => soseq s
  | soterm o bs => soterm o (map (fo_change_bvars_alphabt disj ren) bs)
  end
with fo_change_bvars_alphabt {p} disj ren bt :=
       match bt with
       | sobterm vs t =>
         let vs' := fresh_distinct_vars (length vs) (vs ++ disj ++ all_fo_vars t ++ foren_vars ren) in
         sobterm vs' (fo_change_bvars_alpha disj (mk_foren vs vs' ++ ren) t)
       end.
(* vs in the list of distinct vars above is not necessary but useful *)

Fixpoint so_change_bvars_alpha {p} (disj : list NVar) (ren : soren) (t : @SOTerm p) :=
  match t with
  | sovar v ts =>
    sovar
      (sovar2var (rename_sovar ren (v,length ts)))
      (map (so_change_bvars_alpha disj ren) ts)
  | soseq s => soseq s
  | soterm o bs => soterm o (map (so_change_bvars_alphabt disj ren) bs)
  end
with so_change_bvars_alphabt {p} disj ren bt :=
       match bt with
       | sobterm vs t =>
         let vs' := fresh_distinct_vars (length vs) (disj ++ all_fo_vars t ++ soren_vars ren) in
         sobterm vs' (so_change_bvars_alpha disj (mk_soren (vars2sovars vs) vs' ++ ren) t)
       end.
(* all_fo_vars could just be the free vars above *)

Definition allvars_range_sosub {o} (sub : @SOSub o) : list NVar :=
  flat_map (fun x => allvars_sk (snd x)) sub.

Definition sk_change_bvars_in_alpha {o} (vs : list NVar) (sk : @sosub_kind o) : sosub_kind :=
  match sk with
    | sosk vars t => sosk vars (change_bvars_alpha vs t)
  end.

Definition sosub_change_bvars_in_alpha {o} (vs : list NVar) (sub : @SOSub o) :=
  map (fun x =>
         match x with
           | (v,sk) => (v,sk_change_bvars_in_alpha vs sk)
         end)
      sub.

Definition sk_change_bvars_alpha {o} (vs : list NVar) (sk : @sosub_kind o) : sosub_kind :=
  bterm2sk (change_bvars_alphabt vs (sk2bterm sk)).

Definition sosub_change_bvars_alpha {o} (vs : list NVar) (sub : @SOSub o) :=
  map (fun x =>
         match x with
           | (v,sk) => (v,sk_change_bvars_alpha vs sk)
         end)
      sub.

Definition sosub {o} (sub : @SOSub o) (t : SOTerm) : NTerm :=
  let fvars_s := free_vars_sosub sub in
  let bvars_s := bound_vars_sosub sub in
  let bvars_t := fo_bound_vars t in
  if dec_disjointv bvars_t fvars_s
  then let avars_t := all_fo_vars t in
       if dec_disjointv (fvars_s ++ avars_t) bvars_s
       then sosub_aux sub t
       else sosub_aux
              (sosub_change_bvars_alpha (allvars_range_sosub sub ++ avars_t) sub)
              t
  else let t' := fo_change_bvars_alpha (fvars_s ++ all_fo_vars t) [] t in
       let avars_t := all_fo_vars t' in
       if dec_disjointv (fvars_s ++ avars_t) bvars_s
       then sosub_aux sub t'
       else sosub_aux
              (sosub_change_bvars_alpha (allvars_range_sosub sub ++ avars_t) sub)
              t'.
(* we don't need all the bound vars of sub here, just the once in the terms in the range *)

Definition sk_prog_b {o} (sk : @sosub_kind o) : obool :=
  match sk with
    | sosk vs t => oband (bool2obool (sub_vars (free_vars t) vs)) (wft t)
  end.

Definition sosub_prog_b {o} (sub : @SOSub o) : obool :=
  oball (map (fun x => sk_prog_b (snd x)) sub).

Definition sub2otrue {o} (s : @Sub o) : obool :=
  oball (map (fun x => term2otrue (snd x)) s).

Definition sk2otrue {o} (sk : @sosub_kind o) : obool :=
  match sk with
    | sosk vs t => term2otrue t
  end.

Definition sosub2otrue {o} (s : @SOSub o) : obool :=
  oball (map (fun x => sk2otrue (snd x)) s).

Definition sk_prog {o} (sk : @sosub_kind o) := sk_prog_b sk = sk2otrue sk.

Definition sosub_prog {o} (sub : @SOSub o) := sosub_prog_b sub = sosub2otrue sub.

Definition isprog_sk {o} (sk : @sosub_kind o) :=
  match sk with
    | sosk vs t => isprog_vars vs t
  end.

Definition sk_wf_b {o} (sk : @sosub_kind o) : obool :=
  match sk with
    | sosk vs t => wft t
  end.

Definition sk_wf {o} (sk : @sosub_kind o) := sk_wf_b sk = sk2otrue sk.

Definition sosub_wf_b {o} (sub : @SOSub o) : obool :=
  oball (map (fun x => sk_wf_b (snd x)) sub).

Definition sosub_wf {o} (sub : @SOSub o) := sosub_wf_b sub = sosub2otrue sub.

Lemma sk_prog_b_otrue_implies {o} :
  forall (sk : @sosub_kind o),
    sk_prog_b sk = otrue
    -> sk2otrue sk = otrue.
Proof.
  introv h.
  destruct sk; allsimpl.
  abs_bool2obool q.
  destruct q; allsimpl; auto; ginv.
  apply wft_otrue_implies_term2otrue_otrue; auto.
Qed.

Lemma sk2otrue_ofalse {o} :
  forall (sk : @sosub_kind o), sk2otrue sk = ofalse -> False.
Proof.
  destruct sk; simpl; introv.
  apply term2otrue_not_ofalse.
Qed.

Lemma sosub2otrue_ofalse {o} :
  forall (s : @SOSub o), sosub2otrue s = ofalse -> False.
Proof.
  induction s; introv h; allsimpl; tcsp.
  - unfold sosub2otrue in h; allsimpl; ginv.
  - unfold sosub2otrue in h; allsimpl.
    fold (sosub2otrue s) in h.
    destruct a; allsimpl.
    remember (sosub2otrue s) as ss; symmetry in Heqss; destruct ss; allsimpl.
    + remember (sk2otrue s0) as o1; symmetry in Heqo1.
      destruct o1; allsimpl; ginv.
      apply sk2otrue_ofalse in Heqo1; sp.
    + autodimp IHs hyp; sp.
    + clear IHs.
      remember (sk2otrue s0) as o1; symmetry in Heqo1.
      destruct o1; allsimpl; ginv.
      apply sk2otrue_ofalse in Heqo1; sp.
Qed.

Lemma oband_otrue :
  forall o, oband o otrue = o.
Proof.
  destruct o; allsimpl; auto.
Qed.

Lemma isotrue_sk2otrue {o} :
  forall (sk : @sosub_kind o), isotrue (sk2otrue sk).
Proof.
  destruct sk; simpl.
  apply isotrue_term2otrue.
Qed.

Lemma isotrue_sosub2otrue {o} :
  forall (s : @SOSub o), isotrue (sosub2otrue s).
Proof.
  induction s; introv; simpl; auto.
  unfold sosub2otrue; simpl.
  apply isotrue_oband; dands; auto.
  apply isotrue_sk2otrue.
Qed.

Lemma sk_prog_as_isotrue {o} :
  forall (sk : @sosub_kind o),
    sk_prog sk <=> isotrue (sk_prog_b sk).
Proof.
  unfold sk_prog.
  introv.
  split; intro h.
  - rw h.
    apply isotrue_sk2otrue.
  - destruct sk; allsimpl.
    allrw isotrue_oband; repnd.
    abs_bool2obool b; destruct b; allsimpl; tcsp.
    apply isotrue_wft_implies_eq_term2otrue in h; auto.
Qed.

Lemma sk_wf_as_isotrue {o} :
  forall (sk : @sosub_kind o),
    sk_wf sk <=> isotrue (sk_wf_b sk).
Proof.
  unfold sk_prog.
  introv.
  split; intro h.
  - rw h.
    apply isotrue_sk2otrue.
  - destruct sk; allsimpl.
    allrw isotrue_oband; repnd.
    apply isotrue_wft_implies_eq_term2otrue in h; auto.
Qed.

Lemma sosub_prog_as_isotrue {o} :
  forall (s : @SOSub o),
    sosub_prog s <=> isotrue (sosub_prog_b s).
Proof.
  unfold sosub_prog.
  introv.
  split; intro h.
  - rw h.
    apply isotrue_sosub2otrue.
  - induction s; allsimpl; auto.
    unfold sosub_prog_b in h; allsimpl.
    apply isotrue_oband in h; repnd; allsimpl.
    fold (sosub_prog_b s) in h.
    autodimp IHs hyp.

    unfold sosub_prog_b; simpl.
    fold (sosub_prog_b s).
    rw IHs.
    unfold sosub2otrue; simpl.
    fold (sosub2otrue s).

    apply sk_prog_as_isotrue in h0.
    rw h0; auto.
Qed.

Lemma sosub_wf_as_isotrue {o} :
  forall (s : @SOSub o),
    sosub_wf s <=> isotrue (sosub_wf_b s).
Proof.
  unfold sosub_wf.
  introv.
  split; intro h.
  - rw h.
    apply isotrue_sosub2otrue.
  - induction s; allsimpl; auto.
    unfold sosub_wf_b in h; allsimpl.
    apply isotrue_oband in h; repnd; allsimpl.
    fold (sosub_wf_b s) in h.
    autodimp IHs hyp.

    unfold sosub_wf_b; simpl.
    fold (sosub_wf_b s).
    rw IHs.
    unfold sosub2otrue; simpl.
    fold (sosub2otrue s).

    apply sk_wf_as_isotrue in h0.
    rw h0; auto.
Qed.

Lemma isotrue_oball_map :
  forall A (f : A -> obool) (l : list A),
    isotrue (oball (map f l)) <=> (forall x : A, LIn x l -> isotrue (f x)).
Proof.
  induction l; simpl; tcsp.
  split; intro h; tcsp.
  allrw isotrue_oband.
  rw IHl.
  split; intro h; repnd; dands; auto.
  introv i; repndors; subst; auto.
Qed.

Lemma isotrue_bool2obool_iff :
  forall b : bool, isotrue (bool2obool b) <=> b = true.
Proof.
  introv.
  split; intro h.
  - apply isotrue_bool2obool in h; auto.
  - subst; simpl; auto.
Qed.

Lemma isotrue_wft_implies_eq_term2otrue_iff {o} :
  forall (t : @NTerm o), isotrue (wft t) <=> wft t = term2otrue t.
Proof.
  introv; split; intro h.
  - apply isotrue_wft_implies_eq_term2otrue; auto.
  - rw h.
    apply isotrue_term2otrue.
Qed.

Lemma sosub_prog_prop1 {o} :
  forall (sub : @SOSub o),
    sosub_prog sub
    <=>
    (forall b, LIn b (sorange sub) -> isprogram_bt b).
Proof.
  introv.
  rw @sosub_prog_as_isotrue.
  unfold sosub_prog_b.
  rw isotrue_oball_map.
  split; intro k; introv h.

  - apply in_sorange in h; exrepnd.
    apply k in h0; destruct b; allsimpl.
    allrw isotrue_oband; repnd.
    allapply isotrue_bool2obool.
    fold (assert (sub_vars (free_vars n) l)) in h1.
    fold (subvars (free_vars n) l) in h1.
    constructor; auto.
    + unfold closed_bt; simpl.
      apply null_remove_nvars_subvars in h1; auto.
      rw null_iff_nil in h1; auto.
    + constructor; apply nt_wf_eq; auto.
      apply isotrue_wft_implies_eq_term2otrue in h0; auto.

  - destruct x; destruct s; allsimpl.
    apply isotrue_oband.
    rw isotrue_bool2obool_iff.
    fold (assert (sub_vars (free_vars n0) l)).
    fold (subvars (free_vars n0) l).
    pose proof (k (bterm l n0)) as q.
    autodimp q hyp;[apply in_sorange; simpl; eexists; eauto|].
    inversion q as [c w]; allunfold @closed_bt; allsimpl.
    inversion w; subst.
    allrw @bt_wf_iff.
    rw @isotrue_wft_implies_eq_term2otrue_iff.
    allrw @nt_wf_eq; dands; auto.
    apply null_remove_nvars_subvars; rw c; sp.
Qed.

Lemma sosub_wf_prop1 {o} :
  forall (sub : @SOSub o),
    sosub_wf sub
    <=>
    (forall b, LIn b (sorange sub) -> wf_bterm b).
Proof.
  introv.
  rw @sosub_wf_as_isotrue.
  unfold sosub_prog_b.
  rw isotrue_oball_map.
  split; intro k; introv h.

  - apply in_sorange in h; exrepnd.
    apply k in h0; destruct b; allsimpl.
    unfold wf_bterm; simpl.
    apply isotrue_wft_implies_eq_term2otrue in h0; auto.

  - destruct x; destruct s; allsimpl.
    pose proof (k (bterm l n0)) as q.
    autodimp q hyp;[apply in_sorange; simpl; eexists; eauto|].
    unfold wf_bterm in q; allsimpl.
    rw @isotrue_wft_implies_eq_term2otrue_iff; auto.
Qed.

Lemma isprogram_bt_iff_isprog_vars {o} :
  forall vs (t : @NTerm o),
    isprogram_bt (bterm vs t)
    <=> isprog_vars vs t.
Proof.
  introv.
  unfold isprogram_bt, isprog_vars, closed_bt; simpl.
  rw @bt_wf_iff.
  rw @wf_term_eq.
  rw <- null_iff_nil.
  rw null_remove_nvars_subvars; sp.
Qed.

Lemma sosub_prog_cons {o} :
  forall (sub : @SOSub o) v vs t,
    sosub_prog ((v,sosk vs t) :: sub)
    <=> (isprog_vars vs t # sosub_prog sub).
Proof.
  introv.
  allrw @sosub_prog_prop1; simpl.
  split; intro h; repnd; dands; auto.
  - pose proof (h (bterm vs t)) as q; clear h; autodimp q hyp.
    apply isprogram_bt_iff_isprog_vars; auto.
  - introv i; repndors; subst; auto.
    apply isprogram_bt_iff_isprog_vars; auto.
Qed.

Lemma sosub_prog_cons2 {o} :
  forall (sub : @SOSub o) v sk,
    sosub_prog ((v,sk) :: sub)
    <=> (isprog_sk sk # sosub_prog sub).
Proof.
  introv.
  destruct sk; rw @sosub_prog_cons; simpl; sp.
Qed.

Lemma sosub_wf_cons {o} :
  forall (sub : @SOSub o) v vs t,
    sosub_wf ((v,sosk vs t) :: sub)
    <=> (wf_term t # sosub_wf sub).
Proof.
  introv.
  allrw @sosub_wf_prop1; simpl.
  split; intro h; repnd; dands; auto.
  - pose proof (h (bterm vs t)) as q; clear h; autodimp q hyp.
  - introv i; repndors; subst; auto.
Qed.

Lemma in_sosub_prog {o} :
  forall (sub : @SOSub o) v vs t,
    LIn (v, sosk vs t) sub
    -> sosub_prog sub
    -> isprog_vars vs t.
Proof.
  induction sub; introv i p; allsimpl; tcsp.
  destruct a; destruct s.
  dorn i; cpx; ginv; apply sosub_prog_cons in p; tcsp.
  repnd.
  eapply IHsub; eauto.
Qed.

Lemma in_sosub_wf {o} :
  forall (sub : @SOSub o) v vs t,
    LIn (v, sosk vs t) sub
    -> sosub_wf sub
    -> wf_term t.
Proof.
  induction sub; introv i p; allsimpl; tcsp.
  destruct a; destruct s.
  dorn i; cpx; ginv; apply sosub_wf_cons in p; tcsp.
  repnd.
  eapply IHsub; eauto.
Qed.

Lemma implies_sosub_prog_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    sosub_prog sub
    -> sosub_prog (sosub_filter sub vs).
Proof.
  induction sub; introv h; allsimpl; auto.
  destruct a; destruct s.
  rw @sosub_prog_cons in h; repnd.
  boolvar; auto.
  apply sosub_prog_cons; dands; auto.
Qed.

Lemma implies_sosub_wf_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    sosub_wf sub
    -> sosub_wf (sosub_filter sub vs).
Proof.
  induction sub; introv h; allsimpl; auto.
  destruct a; destruct s.
  rw @sosub_wf_cons in h; repnd.
  boolvar; auto.
  apply sosub_wf_cons; dands; auto.
Qed.

Lemma in_sodom_if {o} :
  forall (sub : @SOSub o) v vs t k,
    LIn (v, sosk vs t) sub
    -> k = length vs
    -> LIn (v,k) (sodom sub).
Proof.
  induction sub; simpl; introv i e; subst; auto.
  destruct a; destruct s; dorn i; cpx; ginv; tcsp.
  eapply IHsub in i; eauto.
Qed.

(*
Fixpoint get_fo_vars (l : list sovar_sig) : list NVar :=
  match l with
    | nil => nil
    | (v,0) :: l => v :: get_fo_vars l
    | _ :: l => get_fo_vars l
  end.
*)

Fixpoint sosize {p} (t : @SOTerm p) : nat :=
  match t with
  | sovar _ ts => S (addl (map sosize ts))
  | soseq s => 0
  | soterm op bs => S (addl (map sosize_bterm bs))
  end
with sosize_bterm {p} (b : SOBTerm) :=
       match b with
         | sobterm _ t => sosize t
       end.

Lemma sosize_in {p} :
  forall (t : @SOTerm p) ts,
    LIn t ts -> sosize t <= addl (map sosize ts).
Proof.
  induction ts; introv i; allsimpl; tcsp.
  dorn i; subst; tcsp; try omega.
  apply IHts in i; try omega.
Qed.

Lemma sosize_bterm_in {p} :
  forall (b : @SOBTerm p) bs,
    LIn b bs -> sosize_bterm b <= addl (map sosize_bterm bs).
Proof.
  induction bs; introv i; allsimpl; tcsp.
  dorn i; subst; tcsp; try omega.
  apply IHbs in i; try omega.
Qed.

Lemma SOTerm_better_ind2 {p} :
  forall P : (@SOTerm p) -> Type,
    (forall v ts,
       (forall t, LIn t ts -> P t)
       -> P (sovar v ts))
    -> (forall s, P (soseq s))
    -> (forall (o : Opid) (bs : list SOBTerm),
          (forall (t t': SOTerm) (vs : list NVar),
             (LIn (sobterm vs t) bs)
              -> sosize t' <= sosize t
              -> P t'
          )
          -> P (soterm o bs)
       )
    -> forall t : SOTerm, P t.
Proof.
  intros P Hvar Hseq Hbt.
  assert (forall n t, sosize t = n -> P t)
    as Hass;
    [ | intros; apply Hass with (n := sosize t); eauto; fail ].

  induction n as [n Hind] using comp_ind_type.
  intros t Hsz.
  destruct t.
  - apply Hvar; allsimpl.
    introv i.
    destruct n; cpx.
    pose proof (Hind (sosize t)) as k; autodimp k hyp.
    apply sosize_in in i; omega.
  - apply Hseq.
  - apply Hbt.
    introv Hin Hs.
    apply Hind with (m := sosize t'); auto.
    subst.
    apply sosize_bterm_in in Hin; allsimpl; omega.
Qed.

Lemma SOTerm_better_ind {p} :
  forall P : @SOTerm p -> Type,
    (forall v ts,
       (forall t, LIn t ts -> P t)
       -> P (sovar v ts))
    -> (forall s, P (soseq s))
    -> (forall (o : Opid) (bs : list SOBTerm),
          (forall t vs, LIn (sobterm vs t) bs -> P t)
          -> P (soterm o bs)
       )
    -> forall t : SOTerm, P t.
Proof.
  introv Hv Hseq Hind.
  apply SOTerm_better_ind2; auto.
  introv Hx.
  apply Hind.
  introv Hin.
  eapply Hx in Hin; eauto.
Qed.

Tactic Notation "soterm_ind" ident(h) ident(c) :=
  induction h using SOTerm_better_ind;
  [ Case_aux c "sovar"
  | Case_aux c "soseq"
  | Case_aux c "soterm"
  ].

Tactic Notation "soterm_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using SOTerm_better_ind;
  [ Case_aux c "sovar"
  | Case_aux c "soseq"
  | Case_aux c "soterm"
  ].

Tactic Notation "soterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using SOTerm_better_ind;
  [ Case_aux c "sovar"
  | Case_aux c "soseq"
  | Case_aux c "soterm"
  ].

Tactic Notation "soterm_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using SOTerm_better_ind2;
  [ Case_aux c "sovar"
  | Case_aux c "soseq"
  | Case_aux c "soterm"
  ].

Lemma sosub_find_some {p} :
  forall (sub : @SOSub p) v n vs t,
    sosub_find sub (v,n) = Some (sosk vs t)
    -> LIn (v, sosk vs t) sub # length vs = n.
Proof.
  induction sub; introv h; allsimpl; tcsp.
  destruct a; destruct s.
  boolvar; subst; simpl in *; ginv; tcsp; apply IHsub in h; tcsp.
Qed.

Lemma sosub_find_none {p} :
  forall (sub : @SOSub p) v n,
    sosub_find sub (v,n) = None
    -> !LIn (v,n) (sodom sub).
Proof.
  induction sub; introv h; allsimpl; tcsp.
  destruct a; destruct s.
  boolvar; subst; ginv; tcsp; apply IHsub in h; tcsp.
  intro xx; repndors; ginv; tcsp.
Qed.

(*
Lemma in_lift_list_option :
  forall T l (k : list T),
    lift_list_option l = Some k
    -> (
         length l = length k
         # (forall t, LIn t k -> LIn (Some t) l)
       ).
Proof.
  induction l; introv lift; allsimpl; ginv; allsimpl; tcsp.
  destruct a; ginv.
  remember (lift_list_option l) as o; destruct o; ginv; allsimpl.
  pose proof (IHl l0) as h; autodimp h hyp; repnd.
  dands; sp; subst; sp.
Qed.
*)

Lemma wf_apply_solist {o} :
  forall (ts : list (@SOTerm o)) f,
    wf_term (apply_list f (map soterm2nterm ts))
    <=> (wf_term f # (forall t, LIn t ts -> wf_soterm t)).
Proof.
  introv.
  rw @wf_apply_list; split; intro k; repd; dands; auto.
  - introv i.
    apply w0.
    rw in_map_iff; exists t; sp.
  - introv i.
    rw in_map_iff in i; exrepnd; subst.
    apply w0 in i1; sp.
Qed.

Lemma wf_sovar {o} :
  forall v (ts : list (@SOTerm o)),
    wf_soterm (sovar v ts)
    <=> (forall t, LIn t ts -> wf_soterm t).
Proof.
  introv; split.
  - introv w i.
    allunfold @wf_soterm; simpl in w.
    allrw @fold_wf_term.
    apply wf_apply_solist in w; repnd.
    apply w; auto.
  - introv w.
    allunfold @wf_soterm; allsimpl.
    apply wf_apply_solist; dands; auto.
    apply wf_term_eq; auto.
Qed.

Lemma wf_soterm_implies {o} :
  forall op (bs : list (@SOBTerm o)),
    wf_soterm (soterm op bs)
    -> forall vs t,
         LIn (sobterm vs t) bs
         -> wf_soterm t.
Proof.
  introv wf i.
  allunfold @wf_soterm.
  apply wf_term_eq in wf; allsimpl.
  inversion wf as [|?|? ? imp e]; subst; clear e.
  pose proof (imp (bterm vs (soterm2nterm t))) as h; clear imp.
  autodimp h hyp.
  - rw in_map_iff.
    eexists; eauto.
  - inversion h; subst.
    apply wf_term_eq; auto.
Qed.

(*
Lemma isprogram_sosub_aux1 {p} :
  forall (t : SOTerm) (sub : @SOSub p) u,
    wf_soterm t
    -> sosub_prog sub
    -> sosub_aux sub t = Some u
    -> isprog u.
Proof.
  soterm_ind t as [ v ts ind | o lbt ind ] Case; simpl; introv wf k e.

  - Case "sovar".
    remember (sosub_find sub v (length ts)) as o;
      destruct o; symmetry in Heqo; simpl; auto; ginv.
    destruct s.
    remember (lift_list_option (map (sosub_aux sub) ts)) as ll;
      destruct ll; symmetry in Heqll; auto; ginv.
    applydup in_lift_list_option in Heqll; repnd.
    allrw map_length.
    applydup @sosub_find_some in Heqo; repnd.
    apply isprog_eq; split.
    + unfold closed.
      rw @isprogram_lsubst_aux2.
      * rw @dom_sub_combine; auto; try omega.
        eapply in_sosub_prog in Heqo1; eauto.
        rw @isprog_vars_eq in Heqo1; repnd.
        apply null_iff_nil.
        apply null_remove_nvars_subvars; auto.
      * introv i.
        apply isprog_eq.
        apply in_combine in i; repnd.
        apply Heqll0 in i; rw in_map_iff in i; exrepnd.
        symmetry in i1.
        apply ind in i1; repnd; auto.
        eapply wf_sovar in wf; eauto.
    + apply nt_wf_eq; apply lsubst_aux_preserves_wf_term.
      * eapply in_sosub_prog in Heqo1; eauto.
        apply isprog_vars_eq in Heqo1; repnd.
        apply wf_term_eq; auto.
      * introv i.
        apply in_combine in i; repnd.
        apply Heqll0 in i; rw in_map_iff in i; exrepnd.
        symmetry in i1.
        apply ind in i1; repnd; auto; [ | eapply wf_sovar in wf; eauto].
        apply isprog_eq in i1; destruct i1 as [c w].
        apply wf_term_eq; auto.

  - Case "soterm".
    remember (lift_list_option (map (sosub_b_aux sub) lbt)).
*)

Lemma remove_so_vars_nil_r :
  forall l, remove_so_vars l [] = [].
Proof.
  unfold remove_so_vars; apply diff_nil.
Qed.

Lemma remove_so_vars_app_r :
  forall l1 l2 l3,
    remove_so_vars l1 (l2 ++ l3) = remove_so_vars l1 l2 ++ remove_so_vars l1 l3.
Proof.
  apply diff_app_r.
Qed.

Lemma remove_so_vars_flat_map :
  forall T,
  forall f : T -> list sovar_sig,
  forall l : list T,
  forall vars : list sovar_sig,
   remove_so_vars vars (flat_map f l) =
   flat_map (compose (remove_so_vars vars) f) l.
Proof.
  induction l; simpl; sp.
  apply remove_so_vars_nil_r.
  rewrite remove_so_vars_app_r.
  rewrite IHl; sp.
Qed.

Lemma sovars2vars_flat_map :
  forall T ts (f : T -> list sovar_sig),
    sovars2vars (flat_map f ts) = flat_map (compose sovars2vars f) ts.
Proof.
  unfold sovars2vars; introv.
  rw map_flat_map; unfold compose; auto.
Qed.

Lemma remove_so_vars_app_l :
  forall l1 l2 l3,
     remove_so_vars l1 (remove_so_vars l2 l3) = remove_so_vars (l1 ++ l2) l3.
Proof.
  apply diff_app_l.
Qed.

Lemma sodom_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    sodom (sosub_filter sub vs) = remove_so_vars vs (sodom sub).
Proof.
  induction sub; simpl; introv.
  - rw remove_so_vars_nil_r; auto.
  - destruct a; destruct s; boolvar; rw remove_so_vars_cons_r; boolvar; simpl; tcsp.
    rw IHsub; auto.
Qed.

Lemma in_sovars2vars :
  forall v vs,
    LIn v (sovars2vars vs)
    <=> {n : nat & LIn (v,n) vs}.
Proof.
  induction vs; simpl; split; intro k; exrepnd; tcsp.
  - dorn k; subst.
    + destruct a.
      exists n0; simpl; tcsp.
    + apply IHvs in k; exrepnd.
      exists n; sp.
  - dorn k0; subst; allsimpl; tcsp.
    destruct a; right; apply IHvs; exists n; sp.
Qed.

Lemma in_remove_so_vars :
  forall x l1 l2,
    LIn x (remove_so_vars l1 l2) <=> (LIn x l2 # ! LIn x l1).
Proof.
  intros; apply in_diff.
Qed.

Lemma so_free_vars_in_all_fo_vars {o} :
  forall (t : @SOTerm o) v n,
    LIn (v, n) (so_free_vars t) -> LIn v (all_fo_vars t).
Proof.
  soterm_ind t as [ v ts ind |  | op lbt ind ] Case; simpl; introv i; tcsp.

  - Case "sovar".
    dorn i; cpx.
    apply lin_flat_map in i; exrepnd.
    apply ind in i0; auto.
    right; rw lin_flat_map.
    exists x; sp.

  - Case "soterm".
    allrw lin_flat_map; exrepnd.
    exists x; sp.
    destruct x; allsimpl.
    rw in_remove_so_vars in i0; repnd.
    rw in_map_iff in i0.
    rw in_app_iff.
    pose proof (in_deq NVar deq_nvar v l) as h; dorn h; tcsp.
    right.
    eapply ind; eauto.
Qed.

Lemma subvars_bound_vars_in_sosub_bound_vars_sosub {o} :
  forall (sub : @SOSub o),
    subvars (bound_vars_in_sosub sub) (bound_vars_sosub sub).
Proof.
  introv; unfold bound_vars_in_sosub, bound_vars_sosub.
  apply subvars_flat_map2; introv i; destruct x; destruct s; simpl.
  apply subvars_app_weak_r; auto.
Qed.

Lemma subvars_bound_vars_in_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    subvars (bound_vars_in_sosub (sosub_filter sub vs)) (bound_vars_in_sosub sub).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; boolvar; simpl.
  - apply subvars_app_weak_r; auto.
  - repeat (rw subvars_app_l); dands.
    + apply subvars_app_weak_l; auto.
    + apply subvars_app_weak_r; auto.
Qed.

Lemma subvars_bound_vars_in_sk {o} :
  forall (sk : @sosub_kind o),
    subvars (bound_vars_in_sk sk) (bound_vars_sk sk).
Proof.
  destruct sk; simpl.
  apply subvars_app_weak_r; auto.
Qed.

Lemma subvars_bound_vars_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    subvars (bound_vars_sosub (sosub_filter sub vs)) (bound_vars_sosub sub).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; boolvar; simpl.
  - apply subvars_app_weak_r; auto.
  - repeat (rw subvars_app_l); dands.
    + repeat (apply subvars_app_weak_l); auto.
    + apply subvars_app_weak_l; apply subvars_app_weak_r; auto.
    + apply subvars_app_weak_r; auto.
Qed.

Lemma free_vars_lsubst_aux_subvars {p} :
  forall (t : NTerm) (sub : @Sub p),
    subvars
      (free_vars (lsubst_aux t sub))
      (remove_nvars (dom_sub sub) (free_vars t) ++ sub_free_vars sub).
Proof.
  nterm_ind t as [ v | f ind | o lbt ind ] Case; simpl; introv.

  - Case "vterm".
    remember (sub_find sub v) as o;
      destruct o; symmetry in Heqo; simpl; auto; ginv.

    + apply sub_find_some in Heqo.
      apply subvars_app_weak_r.
      rw subvars_eq.
      eapply subset_free_vars_mem; eauto.

    + apply subvars_app_weak_l.
      rw subvars_singleton_l.
      rw in_remove_nvars; simpl; dands; tcsp.
      intro k.
      apply in_dom_sub_exists in k; exrepnd.
      rw Heqo in k0; cpx.

  - Case "sterm".
    allrw remove_nvars_nil_r; simpl; auto.

  - Case "oterm".
    rw flat_map_map; unfold compose.
    rw remove_nvars_flat_map; unfold compose.
    rw subvars_prop; introv k.
    rw lin_flat_map in k; exrepnd.
    rw in_app_iff; rw lin_flat_map.
    destruct x0; allsimpl.
    rw in_remove_nvars in k0; repnd.
    dup k1 as j.
    apply ind with (sub := sub_filter sub l) in k1.
    rw subvars_prop in k1; apply k1 in k2.
    rw in_app_iff in k2; dorn k2.

    + rw in_remove_nvars in k2; repnd.
      left.
      eexists; dands; eauto; simpl.
      repeat (rw in_remove_nvars).
      dands; auto; intro k.
      rw <- @dom_sub_sub_filter in k2.
      rw in_remove_nvars in k2; sp.

    + apply in_sub_free_vars in k2; exrepnd.
      rw @in_sub_filter in k3; repnd.
      right.
      apply in_sub_free_vars_iff.
      repeat eexists; eauto.
Qed.

Lemma subvars_free_vars_sosub_mem {o} :
  forall (sub : @SOSub o) v vs t,
    LIn (v, sosk vs t) sub -> subvars (remove_nvars vs (free_vars t)) (free_vars_sosub sub).
Proof.
  induction sub; introv i; allsimpl; tcsp.
  destruct a.
  dorn i; cpx; allsimpl.
  - apply subvars_app_weak_l; auto.
  - apply subvars_app_weak_r.
    eapply IHsub; eauto.
Qed.

Lemma sub_free_vars_combine {o} :
  forall vs (ts : list (@NTerm o)),
    length vs = length ts
    -> sub_free_vars (combine vs ts)
       = flat_map free_vars ts.
Proof.
  induction vs; destruct ts; introv len; allsimpl; tcsp; cpx.
  rw IHvs; auto.
Qed.

Lemma in_sosub_filter {p} :
  forall (sub : @SOSub p) v vs t vars,
    LIn (v,sosk vs t) (sosub_filter sub vars)
    <=>
    (
      LIn (v,sosk vs t) sub
      #
      !LIn (v, length vs) vars
    ).
Proof.
  induction sub; introv; simpl; split; intro k; tcsp;
  destruct a; destruct s; boolvar; allsimpl; tcsp; repnd.
  - rw IHsub in k; sp.
  - dorn k; cpx; ginv; tcsp.
    rw IHsub in k; sp.
  - dorn k0; cpx; ginv; tcsp.
    rw IHsub; sp.
  - dorn k0; cpx; ginv; tcsp.
    rw IHsub; sp.
Qed.

Lemma isprogram_sosub_aux_wf {p} :
  forall (t : SOTerm) (sub : @SOSub p),
    wf_soterm t
    -> sosub_wf sub
    -> wf_term (sosub_aux sub t).
Proof.
  soterm_ind t as [ v ts ind | | o lbt ind ] Case; simpl; introv wft wfs; tcsp.

  - Case "sovar".
    remember (sosub_find sub (v, length ts)) as o;
      destruct o; symmetry in Heqo; simpl; auto; ginv;
      [destruct s|];dands.

    + apply lsubst_aux_preserves_wf_term.
      * apply sosub_find_some in Heqo; repnd.
        eapply in_sosub_wf in Heqo0; eauto.
      * introv i.
        apply in_combine in i; repnd.
        apply in_map_iff in i; exrepnd; subst.
        eapply ind in i2; eauto; repnd; auto.
        eapply wf_sovar in wft; eauto.

    + apply wf_apply_list; dands; auto;[apply wf_term_eq; complete sp|].
      introv i.
      rw in_map_iff in i; exrepnd; subst.
      eapply ind in i1; eauto; repnd; auto.
      eapply wf_sovar in wft; eauto.

  - Case "soterm".
    dands.

    + unfold wf_soterm in wft; simpl in wft.
      apply wf_term_eq in wft.
      inversion wft as [|?| ? ? imp e]; subst.
      rw map_map in e; unfold compose in e.
      apply wf_term_eq.
      constructor.
      * introv i.
        rw in_map_iff in i; exrepnd; subst.
        destruct a; simpl.
        constructor.
        apply wf_term_eq.
        pose proof (imp (bterm l (soterm2nterm s))) as h.
        autodimp h hyp; [rw in_map_iff; eexists; complete eauto|].
        inversion h; subst.
        apply ind with (sub := sosub_filter sub (vars2sovars l)) in i1; repnd; auto;
        [ unfold wf_soterm; apply wf_term_eq; auto
        | apply implies_sosub_wf_sosub_filter; auto
        ].

      * rw <- e.
        rw map_map; unfold compose.
        apply eq_maps; introv i; destruct x; allsimpl; sp.
Qed.

Lemma isprogram_sosub_aux_free_vars {p} :
  forall (t : SOTerm) (sub : @SOSub p),
    subvars
      (free_vars (sosub_aux sub t))
      (sovars2vars (remove_so_vars (sodom sub) (so_free_vars t))
                   ++ free_vars_sosub sub).
Proof.
  soterm_ind t as [ v ts ind | | o lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    remember (sosub_find sub (v, length ts)) as o;
      destruct o; symmetry in Heqo; simpl; auto; ginv;
      [destruct s|];dands.

    + pose proof (free_vars_lsubst_aux_subvars n (combine l (map (sosub_aux sub) ts))) as h.
      eapply subvars_trans;[complete eauto|]; clear h.
      rw subvars_app_l; dands.

      * apply sosub_find_some in Heqo; repnd.
        rw @dom_sub_combine; [|rw map_length; auto].
        apply subvars_app_weak_r.
        eapply subvars_free_vars_sosub_mem; eauto.

      * apply sosub_find_some in Heqo; repnd.
        rw @sub_free_vars_combine; [|rw map_length; auto].
        rw flat_map_map; unfold compose.
        rw subvars_flat_map; introv i.
        dup i as j.
        eapply ind in i; eauto; clear ind.
        eapply subvars_trans;[complete eauto|]; clear i.
        rw subvars_app_l; dands; [|apply subvars_app_weak_r; complete auto].

        apply subvars_app_weak_l.
        rw subvars_prop; introv i.
        allrw in_sovars2vars; exrepnd.
        rw in_remove_so_vars in i0; repnd.
        exists n0; rw in_remove_so_vars; simpl; dands; sp.
        right; rw lin_flat_map.
        exists x; sp.

    + rw @free_vars_apply_list; simpl.
      rw subvars_cons_l.
      apply sosub_find_none in Heqo.
      rw in_app_iff.
      rw in_sovars2vars.
      dands.

      * left.
        exists (length ts).
        rw in_remove_so_vars; simpl; sp.

      * rw subvars_flat_map; introv i.
        rw in_map_iff in i; exrepnd; subst.
        dup i1 as j.
        eapply ind in i1; clear ind.
        eapply subvars_trans;[complete eauto|]; clear i1.
        rw subvars_app_l; dands; [|apply subvars_app_weak_r; complete auto].

        apply subvars_app_weak_l.
        rw subvars_prop; introv i.
        allrw in_sovars2vars; exrepnd.
        rw in_remove_so_vars in i0; repnd.
        exists n; rw in_remove_so_vars; simpl; dands; sp.
        right; rw lin_flat_map.
        exists a; sp.

  - Case "soterm".
    dands.

    + rw flat_map_map.
      rw remove_so_vars_flat_map.
      rw sovars2vars_flat_map.
      unfold compose.
      rw subvars_prop; introv i.
      rw lin_flat_map in i; exrepnd.
      destruct x0; allsimpl.
      rw in_remove_nvars in i0; repnd.
      rw in_app_iff.
      dup i1 as j.
      apply ind with (sub := sosub_filter sub (vars2sovars l)) in i1; clear ind.

      repnd.
      rw subvars_prop in i1; apply i1 in i2; clear i1.
      rw in_app_iff in i2.
      rw in_sovars2vars in i2.
      rw lin_flat_map.
      dorn i2; exrepnd.

      * rw in_remove_so_vars in i1; repnd.
        rw @sodom_sosub_filter in i1.
        rw in_remove_so_vars in i1.
        pose proof (in_deq sovar_sig sovar_sig_dec (x,n) (sodom sub)) as d.
        apply not_over_and in i1; auto.
        dorn i1.

        left.
        eexists; dands; eauto; simpl.
        rw in_sovars2vars.
        exists n.
        rw in_remove_so_vars; dands; tcsp.
        rw in_remove_so_vars; dands; tcsp.
        rw in_map_iff.
        unfold var2sovar; intro k; exrepnd; cpx.

        provefalse.
        destruct i1.
        intro i1.
        rw in_map_iff in i1; exrepnd.
        allunfold var2sovar; cpx.

      * rw lin_flat_map in i2; exrepnd; allsimpl.
        destruct x0.
        rw @in_sosub_filter in i2; repnd; allsimpl.
        allrw in_remove_nvars; repnd.
        allrw in_map_iff.
        right.
        rw lin_flat_map.
        eexists; dands; eauto; simpl.
        rw in_remove_nvars; sp.
Qed.

Lemma sosub_prog_implies_wf {o} :
  forall (sub : @SOSub o),
    sosub_prog sub -> sosub_wf sub.
Proof.
  introv prog.
  rw @sosub_prog_prop1 in prog.
  rw @sosub_wf_prop1.
  introv i.
  apply prog in i.
  destruct b as [l t].
  apply @isprogram_bt_iff_isprog_vars in i.
  apply bt_wf_eq.
  apply bt_wf_iff.
  apply isprog_vars_eq in i; sp.
Qed.

Lemma implies_null_flat_map :
  forall (A B : Type) (f : A -> list B) (l : list A),
    (forall a, LIn a l -> null (f a))
    -> null (flat_map f l).
Proof.
  induction l; simpl; introv h; tcsp.
  rw null_app; dands; tcsp.
Qed.

Lemma sk2bterm2sk {o} :
  forall sk : @sosub_kind o, bterm2sk (sk2bterm sk) = sk.
Proof.
  destruct sk; simpl; auto.
Qed.

Lemma sosub_prog_implies_free_vars_nil {o} :
  forall (sub : @SOSub o),
    sosub_prog sub -> free_vars_sosub sub = [].
Proof.
  introv prog.
  rw @sosub_prog_prop1 in prog.
  apply null_iff_nil.
  apply implies_null_flat_map; introv i.
  destruct a as [v sk]; allsimpl.
  pose proof (prog (sk2bterm sk)) as h; clear prog.
  destruct sk; allsimpl.
  autodimp h hyp.
  { apply in_sorange; exists v; auto. }
  apply null_remove_nvars_subvars; auto.
  apply isprogram_bt_iff_isprog_vars in h.
  apply isprog_vars_eq in h; sp.
Qed.

Lemma isprogram_sosub_aux1 {p} :
  forall (t : SOTerm) (sub : @SOSub p),
    wf_soterm t
    -> sosub_prog sub
    -> let u := sosub_aux sub t
       in wf_term u
          # subvars
              (free_vars u)
              (sovars2vars (remove_so_vars (sodom sub) (so_free_vars t))).
Proof.
  introv wf prog; simpl.
  applydup @sosub_prog_implies_free_vars_nil in prog.
  applydup @sosub_prog_implies_wf in prog.
  pose proof (isprogram_sosub_aux_wf t sub wf prog1) as h1;
    pose proof (isprogram_sosub_aux_free_vars t sub) as h2;
    rw prog0 in h2; rw app_nil_r in h2; dands; auto.
Qed.

Definition num_sobvars {o} (b : @SOBTerm o) :=
  match b with
    | sobterm vs t => length vs
  end.

Lemma wf_soterm_iff {o} :
  forall op (bs : list (@SOBTerm o)),
    wf_soterm (soterm op bs)
    <=>
    (
      map (num_sobvars) bs = OpBindings op
      # forall vs t,
          LIn (sobterm vs t) bs
          -> wf_soterm t
    ).
Proof.
  introv.
  unfold wf_soterm; simpl.
  rw @wf_term_eq.
  split; intro k; repnd; dands.
  - inversion k as [|?|? ? imp e]; subst.
    rw <- e; rw map_map; unfold compose; apply eq_maps; introv i.
    destruct x; simpl; unfold num_bvars; auto.
  - inversion k as [|?|? ? imp e]; subst.
    introv i.
    pose proof (imp (bterm vs (soterm2nterm t))) as h; autodimp h hyp.
    rw in_map_iff; eexists; dands; eauto.
    inversion h; subst; auto.
    apply wf_term_eq; auto.
  - constructor.
    + introv i.
      destruct l; rw in_map_iff in i; exrepnd; subst.
      destruct a; allsimpl; ginv.
      apply k in i1.
      constructor; apply nt_wf_eq; auto.
    + rw <- k0.
      rw map_map; unfold compose; apply eq_maps; introv i.
      destruct x; simpl; unfold num_bvars; simpl; auto.
Qed.

Ltac gen_fresh :=
  let f := fresh "f" in
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f;
        match goal with
          | [ H : f = fresh_distinct_vars a b |- _ ] =>
            apply fresh_distinct_vars_spec1 in H; repnd
        end
  end.

Lemma wf_soterm_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) disj ren,
    wf_soterm t <=> wf_soterm (fo_change_bvars_alpha disj ren t).
Proof.
  soterm_ind t as [ v ts ind | | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; allrw @wf_sovar; allsimpl; tcsp.
    split; intro k; introv i.
    + rw in_map_iff in i; exrepnd; subst.
      apply ind; auto.
    + pose proof (k (fo_change_bvars_alpha disj ren t)) as h;
        autodimp h hyp; [ rw in_map_iff; eexists; complete sp | ].
      eapply ind in h; eauto.

  - Case "soterm".
    allrw @wf_soterm_iff; rw map_map; unfold compose.
    split; intro k; repnd; dands.

    + rw <- k0; apply eq_maps; introv i.
      destruct x; simpl.
      gen_fresh; auto.

    + introv i.
      rw in_map_iff in i; exrepnd.
      destruct a; allsimpl; ginv.
      pose proof (ind s l i1) as h.
      rw <- h; auto.
      eapply k; eauto.

    + rw <- k0; apply eq_maps; introv i.
      destruct x; simpl.
      gen_fresh; auto.

    + introv i.
      pose proof (k (fresh_distinct_vars (length vs) (vs ++ disj ++ all_fo_vars t ++ foren_vars ren))
                    (fo_change_bvars_alpha
                       disj
                       (mk_foren vs (fresh_distinct_vars (length vs) (vs ++ disj ++ all_fo_vars t ++ foren_vars ren)) ++ ren) t)) as h.
      autodimp h hyp.
      * rw in_map_iff; eexists; dands; eauto.
      * eapply ind in h; eauto.
Qed.

Lemma wf_soterm_so_change_bvars_alpha {o} :
  forall (t : @SOTerm o) disj ren,
    wf_soterm t <=> wf_soterm (so_change_bvars_alpha disj ren t).
Proof.
  soterm_ind t as [ v ts ind | | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    split; intro k; apply wf_sovar; allsimpl; introv i; tcsp.
    + rw in_map_iff in i; exrepnd; subst.
      apply ind; auto.
      eapply wf_sovar in k; eauto.
    + rw @wf_sovar in k.
      pose proof (k (so_change_bvars_alpha disj ren t)) as h;
        autodimp h hyp; [ rw in_map_iff; eexists; complete sp | ].
      eapply ind in h; eauto.

  - Case "soterm".
    allunfold @wf_soterm; allsimpl.
    repeat (rw @wf_term_eq).
    split; intro wf.
    + inversion wf as [|?| ? ? imp e]; subst; clear wf.
      constructor.
      * introv i.
        rw in_map_iff in i; exrepnd; subst.
        rw in_map_iff in i1; exrepnd; subst.
        destruct a0; allsimpl.
        constructor.
        rw @nt_wf_eq.
        pose proof (imp (bterm l (soterm2nterm s))) as h.
        autodimp h hyp; [rw in_map_iff; eexists; complete eauto|].
        inversion h; subst.
        eapply ind in i1.
        rw <- i1; auto.
        apply wf_term_eq; auto.
      * rw <- e.
        allrw map_map; unfold compose.
        apply eq_maps; introv i.
        destruct x; simpl; unfold num_bvars; simpl.
        rw length_fresh_distinct_vars; auto.
    + inversion wf as [|?| ? ? imp e]; subst; clear wf.
      constructor.
      * introv i; rw in_map_iff in i; exrepnd; subst.
        destruct a; simpl.
        constructor.
        apply wf_term_eq.
        pose proof (imp (bterm
                           (fresh_distinct_vars (length l) (disj ++ all_fo_vars s ++ soren_vars ren))
                           (soterm2nterm
                              (so_change_bvars_alpha
                                 disj
                                 (mk_soren (vars2sovars l) (fresh_distinct_vars (length l) (disj ++ all_fo_vars s ++ soren_vars ren)) ++ ren) s)))) as h.
        autodimp h hyp.
        rw map_map; unfold compose.
        rw in_map_iff; eexists; dands; eauto; simpl.
        inversion h; subst.
        allrw @nt_wf_eq.
        eapply ind; eauto.
      * rw <- e.
        allrw map_map; unfold compose.
        apply eq_maps; introv i.
        destruct x; simpl; unfold num_bvars; simpl.
        rw length_fresh_distinct_vars; auto.
Qed.

Lemma rename_sovar_foren2soren_fo :
  forall ren v,
    rename_sovar (foren2soren ren) (v, 0) = (rename_var ren v, 0).
Proof.
  induction ren; introv; simpl; auto.
  destruct a; simpl.
  unfold var2sovar; rw rename_sovar_cons; rw rename_var_cons; boolvar; cpx.
Qed.

Lemma rename_sovar_foren2soren_so :
  forall ren v n,
    n > 0
    -> rename_sovar (foren2soren ren) (v, n) = (v, n).
Proof.
  induction ren; introv k; simpl; auto.
  destruct a; simpl.
  unfold var2sovar; rw rename_sovar_cons; boolvar; cpx; omega.
Qed.

Lemma sovar2var_rename_sovar :
  forall ren v n,
    (sovar2var (rename_sovar ren (v, n)), n)
    = rename_sovar ren (v, n).
Proof.
  induction ren; introv; simpl; tcsp.
  destruct a; destruct s.
  rw rename_sovar_cons; boolvar; simpl; cpx.
Qed.

Lemma sovars2vars_so_free_vars_subvars_all_fo_vars {o} :
  forall (t : @SOTerm o),
    subvars (sovars2vars (so_free_vars t)) (all_fo_vars t).
Proof.
  soterm_ind t as [ v ts ind | | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    apply subvars_cons_lr.
    rw sovars2vars_flat_map.
    apply subvars_flat_map2.
    introv i; unfold compose; auto.

  - Case "soterm".
    rw sovars2vars_flat_map.
    apply subvars_flat_map2; introv i.
    destruct x; unfold compose; simpl.
    apply ind in i.
    allrw subvars_prop.
    introv k.
    apply in_sovars2vars in k; exrepnd.
    apply in_remove_so_vars in k0; repnd.
    rw in_map_iff in k0.

    pose proof (i x) as h.
    autodimp h hyp.
    apply in_sovars2vars.
    exists n; auto.
    rw in_app_iff. sp.
Qed.

Lemma soren_find_app :
  forall v ren1 ren2,
    soren_find (ren1 ++ ren2) v
    = match soren_find ren1 v with
        | Some w => Some w
        | None => soren_find ren2 v
      end.
Proof.
  induction ren1; simpl; sp.
  destruct a0; destruct v; boolvar; cpx.
Qed.

Lemma soren_find_some :
  forall (ren : soren) v n w,
    soren_find ren (v,n) = Some w
    -> {z : NVar & LIn ((v,n),z) ren # w = (z,n)}.
Proof.
  induction ren; simpl; sp.
  destruct a0; boolvar; subst; simpl in *; cpx.
  - exists a; sp.
  - discover; exrepnd; subst.
    eexists; sp.
  - discover; exrepnd; subst.
    eexists; sp.
Qed.

Lemma soren_find_none :
  forall (ren : soren) v,
    soren_find ren v = None
    -> !LIn v (soren_dom ren).
Proof.
  induction ren; introv k; allsimpl; tcsp.
  destruct a; destruct s; boolvar; cpx.
  apply IHren in k.
  apply not_over_or; sp.
Qed.

Lemma in_foren2soren :
  forall ren v1 v2 n,
    LIn (v1, n, v2) (foren2soren ren)
    <=> (n = 0 # LIn (v1,v2) ren).
Proof.
  induction ren; introv; simpl; split; intro k; tcsp; destruct a.
  - unfold var2sovar in k.
    dorn k; cpx.
    apply IHren in k; sp.
  - unfold var2sovar; repnd; subst; dorn k; cpx.
    right; apply IHren; auto.
Qed.

Lemma in_mk_foren :
  forall v1 v2 vs1 vs2,
    LIn (v1,v2) (mk_foren vs1 vs2)
    -> LIn v1 vs1 # LIn v2 vs2.
Proof.
  induction vs1; introv i; allsimpl; tcsp.
  destruct vs2; allsimpl; tcsp.
  dorn i; cpx.
  apply IHvs1 in i; repnd; sp.
Qed.

Lemma in_mk_soren :
  forall v1 v2 vs1 vs2,
    LIn (v1,v2) (mk_soren vs1 vs2)
    -> LIn v1 vs1 # LIn v2 vs2.
Proof.
  induction vs1; introv i; allsimpl; tcsp.
  destruct vs2; allsimpl; tcsp.
  dorn i; cpx.
  apply IHvs1 in i; repnd; sp.
Qed.

Lemma in_foren_implies_in_vars :
  forall v1 v2 ren,
    LIn (v1,v2) ren -> LIn v1 (foren_vars ren) # LIn v2 (foren_vars ren).
Proof.
  induction ren; introv i; allsimpl; tcsp.
  destruct a; simpl.
  dorn i; cpx.
Qed.

Lemma in_soren_implies_in_vars :
  forall v1 v2 ren,
    LIn (v1,v2) ren -> LIn (sovar2var v1) (soren_vars ren) # LIn v2 (soren_vars ren).
Proof.
  induction ren; introv i; allsimpl; tcsp.
  destruct a; destruct s; simpl.
  dorn i; cpx.
Qed.

Lemma soren_dom_foren2soren :
  forall ren : foren,
    soren_dom (foren2soren ren) = vars2sovars (foren_dom ren).
Proof.
  induction ren; simpl; auto.
  destruct a; simpl; rw IHren; auto.
Qed.

Lemma rename_sovar_app_weak_l :
  forall ren1 ren2 v,
    !LIn v (soren_dom ren1)
    -> rename_sovar (ren1 ++ ren2) v = rename_sovar ren2 v.
Proof.
  induction ren1; introv ni; allsimpl; auto.
  destruct a; destruct s; allsimpl.
  rw not_over_or in ni; repnd.
  rw rename_sovar_cons; boolvar; subst; sp.
Qed.

Lemma so_free_vars_so_change_bvars_alpha {o} :
  forall (t : @SOTerm o) (disj : list NVar) (ren : soren),
    so_free_vars (so_change_bvars_alpha disj ren t)
    = map (rename_sovar ren) (so_free_vars t).
Proof.
  soterm_ind t as [ v ts ind | | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    apply eq_cons.
    + rw map_length.
      apply sovar2var_rename_sovar.
    + rw map_flat_map.
      rw flat_map_map.
      unfold compose.
      apply eq_flat_maps; introv i.
      apply ind; auto.

  - Case "soterm".
    rw flat_map_map.
    rw map_flat_map.
    unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    pose proof (fresh_distinct_vars_spec (length l) (disj ++ all_fo_vars s ++ soren_vars ren))
      as spec; simpl in spec; repnd.
    remember (fresh_distinct_vars (length l) (disj ++ all_fo_vars s ++ soren_vars ren))
      as f; clear Heqf.
    erewrite ind; eauto; clear ind.
    remember (so_free_vars s) as vars.
    allrw disjoint_app_r; repnd.

    assert (disjoint f (sovars2vars vars))
      as d
        by (subst; eapply subvars_disjoint_r;
            [ complete apply sovars2vars_so_free_vars_subvars_all_fo_vars
            | auto ]).

    clear Heqvars i disj s lbt op o spec0 spec3 spec2.
    revert ren l f d spec1 spec.
    induction vars; simpl; introv d1 d2 len.
    + allrw remove_so_vars_nil_r; simpl; auto.
    + rw disjoint_cons_r in d1; repnd.
      allrw remove_so_vars_cons_r; boolvar; simpl; auto.

      * provefalse; clear IHvars.
        allrw in_map_iff; exrepnd.
        unfold rename_sovar in l1.
        rw soren_find_app in l1.
        remember (soren_find (mk_soren (vars2sovars l) f) a) as o;
          symmetry in Heqo; destruct o; subst.

        { unfold var2sovar in Heqo.
          destruct a.
          apply soren_find_some in Heqo; exrepnd; cpx.
          apply in_mk_soren in Heqo1; repnd; GC.
          rw in_map_iff in Heqo0; exrepnd; destruct a; allunfold var2sovar; cpx.
          apply n; exists (nvar v); sp. }

        { remember (soren_find ren a) as p;
            symmetry in Heqp; destruct p; subst.

          unfold var2sovar in Heqp.
          destruct a.
          apply soren_find_some in Heqp; exrepnd; cpx.
          apply in_soren_implies_in_vars in Heqp1; sp.
          apply d2 in l0; sp.

          unfold sovar2var, var2sovar in d1; simpl in d1; sp. }

      * provefalse; clear IHvars.
        allrw in_map_iff; exrepnd; subst.
        unfold sovar2var, var2sovar in d1; simpl in d1.
        unfold rename_sovar in n.
        rw soren_find_app in n.
        remember (soren_find (mk_soren (vars2sovars l) f) (var2sovar a0)) as o;
          symmetry in Heqo; destruct o; subst.

        apply soren_find_some in Heqo; exrepnd; subst.
        apply in_mk_soren in Heqo1; repnd.
        apply n; clear n.
        exists z; sp.

        apply soren_find_none in Heqo.
        rw soren_dom_mk_soren in Heqo; [|unfold vars2sovars; rw map_length; complete auto].
        rw in_map_iff in Heqo; apply Heqo; exists a0; sp.

      * apply eq_cons; [|apply IHvars; complete auto].
        apply rename_sovar_app_weak_l.
        rw soren_dom_mk_soren; auto.
        unfold vars2sovars; rw map_length; auto.
Qed.

Lemma so_free_vars_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) (disj : list NVar) (ren : foren),
    so_free_vars (fo_change_bvars_alpha disj ren t)
    = map (rename_sovar (foren2soren ren)) (so_free_vars t).
Proof.
  soterm_ind t as [ v ts ind | | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl.
    + rw rename_sovar_foren2soren_fo; auto.
    + rw map_length.
      rw map_flat_map; rw flat_map_map; unfold compose.
      rw rename_sovar_foren2soren_so;[|destruct ts; allsimpl; cpx; omega].
      apply eq_cons; auto.
      apply eq_flat_maps; sp.

  - Case "soterm".
    rw flat_map_map; rw map_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    gen_fresh.

    erewrite ind; eauto; clear ind.
    remember (so_free_vars s) as vars.
    allrw disjoint_app_r; repnd.

    assert (disjoint f (sovars2vars vars))
      as d
        by (subst; eapply subvars_disjoint_r;
            [ complete apply sovars2vars_so_free_vars_subvars_all_fo_vars
            | auto ]).

    clear Heqvars i disj s lbt op o Heqf0 Heqf3 Heqf2 Heqf4.
    revert ren l f d Heqf1 Heqf.
    induction vars; simpl; introv d1 d2 len.
    + allrw remove_so_vars_nil_r; simpl; auto.
    + rw disjoint_cons_r in d1; repnd.
      allrw remove_so_vars_cons_r; boolvar; simpl; auto.

      * provefalse; clear IHvars.
        allrw in_map_iff; exrepnd.
        unfold rename_sovar in l1.
        rw foren2soren_app in l1.
        rw soren_find_app in l1.
        remember (soren_find (foren2soren (mk_foren l f)) a) as o;
          symmetry in Heqo; destruct o; subst.

        {
          unfold var2sovar in Heqo.
          destruct a.
          apply soren_find_some in Heqo; exrepnd; cpx.
          apply in_foren2soren in Heqo1; repnd; GC.
          apply in_mk_foren in Heqo1; repnd; GC; allsimpl.
          destruct n; allunfold var2sovar; cpx.
          eexists; eauto.
        }

        {
          remember (soren_find (foren2soren ren) a) as p;
          symmetry in Heqp; destruct p; subst.

          {
            unfold var2sovar in Heqp.
            destruct a.
            apply soren_find_some in Heqp; exrepnd; cpx.
            apply in_foren2soren in Heqp1; repnd; allsimpl; GC.
            apply d2 in l0; sp.
            apply in_foren_implies_in_vars in Heqp1; sp.
          }

          {
            unfold sovar2var, var2sovar in d1; simpl in d1; sp.
          }
        }

      * provefalse; clear IHvars.
        allrw in_map_iff; exrepnd; subst.
        unfold sovar2var, var2sovar in d1; allsimpl.
        unfold rename_sovar in n.
        rw foren2soren_app in n.
        rw soren_find_app in n.
        remember (soren_find (foren2soren (mk_foren l f)) (var2sovar a0)) as o;
          symmetry in Heqo; destruct o; subst.

        {
          apply soren_find_some in Heqo; exrepnd; subst.
          apply in_foren2soren in Heqo1; repnd; GC.
          apply in_mk_foren in Heqo1; repnd; GC.
          destruct n.
          eexists; eauto.
        }

        {
          apply soren_find_none in Heqo.
          rw soren_dom_foren2soren in Heqo.
          rw foren_dom_mk_foren in Heqo; auto.
          rw in_map_iff in Heqo; destruct Heqo; eexists; eauto.
        }

      * apply eq_cons; [|apply IHvars; complete auto].
        rw foren2soren_app.
        apply rename_sovar_app_weak_l.
        rw soren_dom_foren2soren.
        rw foren_dom_mk_foren; auto.
Qed.

Lemma map_rename_sovar_nil :
  forall vs, map (rename_sovar []) vs = vs.
Proof.
  induction vs; simpl; auto.
  rw IHvs; auto.
Qed.

Lemma disjoint_bound_vars_in_sk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    subvars vs1 vs2
    -> disjoint vs1 (bound_vars_in_sk (sk_change_bvars_in_alpha vs2 sk)).
Proof.
  destruct sk; simpl; introv sv.
  pose proof (change_bvars_alpha_spec n vs2) as h; simpl in h; repnd.
  eapply subvars_disjoint_l; eauto.
Qed.

Lemma disjoint_bound_vars_in_sosub {o} :
  forall (sub : @SOSub o) vs1 vs2,
    subvars vs1 vs2
    -> disjoint vs1 (bound_vars_in_sosub (sosub_change_bvars_in_alpha vs2 sub)).
Proof.
  induction sub; introv sv; simpl; auto.
  destruct a; simpl.
  rw disjoint_app_r; dands; auto.
  apply disjoint_bound_vars_in_sk; auto.
Qed.

Lemma disjoint_bound_vars_sk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    subvars vs1 vs2
    -> disjoint vs1 (bound_vars_sk (sk_change_bvars_alpha vs2 sk)).
Proof.
  destruct sk; simpl; introv sv.
  pose proof (change_bvars_alpha_spec n vs2) as h; simpl in h; repnd.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd.
  allrw disjoint_app_r; repnd; dands; auto.
  - eapply subvars_disjoint_l; eauto; apply disjoint_sym; auto.
  - rw @boundvars_lsubst_aux_vars; auto.
    eapply subvars_disjoint_l; eauto.
Qed.

Lemma disjoint_bound_vars_sosub {o} :
  forall (sub : @SOSub o) vs1 vs2,
    subvars vs1 vs2
    -> disjoint vs1 (bound_vars_sosub (sosub_change_bvars_alpha vs2 sub)).
Proof.
  induction sub; introv sv; simpl; auto.
  destruct a; simpl.
  rw disjoint_app_r; dands; auto.
  apply disjoint_bound_vars_sk; auto.
Qed.

Lemma alphaeq_preserves_isprog_vars {o} :
  forall (t1 t2 : @NTerm o) vs,
    alpha_eq t1 t2
    -> isprog_vars vs t1
    -> isprog_vars vs t2.
Proof.
  introv aeq prog.
  pose proof (alphaeq_preserves_wf t1 t2 aeq) as h.
  pose proof (alphaeq_preserves_free_vars t1 t2 aeq) as k.
  allrw @isprog_vars_eq; repnd.
  rw h; rw <- k; dands; auto.
Qed.

Lemma isprog_vars_change_bvars_alpha {o} :
  forall (t : @NTerm o) l vs,
    isprog_vars l t
    <=> isprog_vars l (change_bvars_alpha vs t).
Proof.
  introv; split; intro prog.
  - pose proof (change_bvars_alpha_spec t vs) as h; simpl in h; repnd.
    eapply alphaeq_preserves_isprog_vars;[|complete eauto];auto.
  - pose proof (change_bvars_alpha_spec t vs) as h; simpl in h; repnd.
    eapply alphaeq_preserves_isprog_vars;[|complete eauto];auto.
    apply alpha_eq_sym; auto.
Qed.

Lemma remove_nvars_comp :
  forall l1 l2 l3,
    remove_nvars l1 (remove_nvars l2 l3)
    = remove_nvars l1 (remove_nvars (remove_nvars l1 l2) l3).
Proof.
  introv.
  allrw remove_nvars_app_l.
  induction l3.
  - allrw remove_nvars_nil_r; auto.
  - allrw remove_nvars_cons_r; boolvar; tcsp;
    allrw in_app_iff; allrw not_over_or; repnd;
    allrw in_remove_nvars; tcsp.
    + dorn Heqb; provefalse; sp.
    + rw IHl3; auto.
Qed.

Lemma remove_nvars_if_eqvars :
  forall vs vs1 vs2,
    eqvars vs1 vs2
    -> remove_nvars vs1 vs = remove_nvars vs2 vs.
Proof.
  induction vs; introv eqv; allsimpl.
  - allrw remove_nvars_nil_r; auto.
  - allrw remove_nvars_cons_r; boolvar; tcsp.
    + rw eqvars_prop in eqv; apply eqv in Heqb; sp.
    + rw eqvars_prop in eqv; apply eqv in Heqb0; sp.
    + apply IHvs in eqv; rw eqv; auto.
Qed.

Lemma eqvars_remove_nvars_app :
  forall vs1 vs2, subvars vs1 vs2 -> eqvars ((remove_nvars vs1 vs2) ++ vs1) vs2.
Proof.
  introv sv; rw eqvars_prop; introv; rw in_app_iff; rw in_remove_nvars;
  split; intro k; tcsp.
  - dorn k; tcsp.
    rw subvars_prop in sv; sp.
  - destruct (in_deq NVar deq_nvar x vs1); tcsp.
Qed.

Lemma free_vars_lsubst_aux_var_ren {o} :
  forall (t : @NTerm o) vs1 vs2 vs,
    disjoint vs2 (free_vars t)
    -> disjoint vs2 (bound_vars t)
    -> length vs1 = length vs2
    -> remove_nvars (vs2 ++ vs) (free_vars (lsubst_aux t (var_ren vs1 vs2)))
       = remove_nvars (vs1 ++ vs) (free_vars t).
Proof.
  nterm_ind t as [v|f induction|op bs ind] Case; introv disj1 disj2 len; allsimpl; auto.

  - Case "vterm".
    rw disjoint_singleton_r in disj1.
    remember (sub_find (var_ren vs1 vs2) v) as f; symmetry in Heqf; destruct f; simpl.
    + apply sub_find_some in Heqf.
      apply in_var_ren in Heqf; exrepnd; subst; simpl.
      allrw remove_nvars_cons_r; boolvar; tcsp;
      allrw remove_nvars_nil_r; auto;
      provefalse; allrw in_app_iff; allrw not_over_or; tcsp.

    + apply sub_find_none2 in Heqf.
      rw @dom_sub_var_ren in Heqf; auto.
      allrw remove_nvars_cons_r; boolvar; tcsp;
      allrw remove_nvars_nil_r; auto;
      provefalse; allrw in_app_iff; allrw not_over_or; tcsp.

  - Case "sterm".
    allrw remove_nvars_nil_r; auto.

  - Case "oterm".
    rw flat_map_map; unfold compose.
    allrw remove_nvars_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    allrw remove_nvars_app_l.

    pose proof (@sub_filter_var_ren_implies o vs1 vs2 l) as h; exrepnd.
    rw h0.

    autodimp h1 hyp.
    assert (eqvars ((vs1 ++ vs) ++ l) ((vs3 ++ vs) ++ l)) as k.
    {
      allrw eqvars_prop; introv; allrw in_app_iff; split; intro h; dorn h; tcsp.
      {
        destruct (in_deq NVar deq_nvar x l); tcsp.
        rw h2; left; rw in_remove_nvars; sp.
      }
      {
        rw h2 in h; rw in_remove_nvars in h; sp.
      }
    }

    apply remove_nvars_if_eqvars with (vs := free_vars n) in k; rw k; clear k.
    applydup eqvars_remove_nvars_app in h3.
    assert (eqvars (((remove_nvars vs4 vs2 ++ vs4) ++ vs) ++ l) ((vs2 ++ vs) ++ l))
      as eqv by (apply eqvars_app; auto; apply eqvars_app; auto).

    apply remove_nvars_if_eqvars with (vs := free_vars (lsubst_aux n (var_ren vs3 vs4)))
      in eqv; rw <- eqv; clear eqv.

    rw <- app_assoc.
    rw <- app_assoc.
    rw <- remove_nvars_app_l.
    rw <- app_assoc.
    pose proof (ind n l i vs3 vs4 (vs ++ l)) as h; repeat (autodimp h hyp).

    + allrw disjoint_flat_map_r.
      applydup disj1 in i; applydup disj2 in i; allsimpl.
      allrw disjoint_app_r; repnd.
      introv a b.
      rw subvars_prop in h3; apply h3 in a; clear h3.
      applydup i0 in a.
      applydup i2 in a.
      rw in_remove_nvars in a0; destruct a0; sp.

    + allrw disjoint_flat_map_r.
      apply disj2 in i; simpl in i.
      rw disjoint_app_r in i; repnd.
      eapply subvars_disjoint_l; eauto.

    + rw h.
      assert (disjoint
                (remove_nvars vs4 vs2)
                (remove_nvars (vs3 ++ vs ++ l) (free_vars n))) as disj.

      * introv a b.
        allrw in_remove_nvars; repnd; allrw in_app_iff; allrw not_over_or; repnd.
        allrw disjoint_flat_map_r.
        apply disj1 in i; simpl in i.
        apply i in a0; rw in_remove_nvars in a0; sp.

      * apply disjoint_sym in disj.
        apply remove_nvars_unchanged in disj.
        rw disj; auto.
Qed.

Lemma free_vars_change_bvars_alpha {o} :
  forall (t : @NTerm o) vs,
    free_vars (change_bvars_alpha vs t) = free_vars t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; auto.
  rw flat_map_map; unfold compose; apply eq_flat_maps; introv i.
  destruct x; simpl.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd.
  allrw disjoint_app_r; repnd.
  pose proof (ind n l i vs) as h.

  pose proof (free_vars_lsubst_aux_var_ren (change_bvars_alpha vs n) l f []) as k.
  repeat (autodimp k hyp).
  allrw app_nil_r.
  rw k; rw h; auto.
Qed.

Lemma isprog_sk_change_bvars_alpha {o} :
  forall (sk : @sosub_kind o) vs,
    isprog_sk sk
    <=> isprog_sk (sk_change_bvars_alpha vs sk).
Proof.
  destruct sk; introv; simpl.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd.
  allrw disjoint_app_r; repnd.
  allrw @isprog_vars_eq.
  pose proof (@allvars_combine o l f) as h.
  eapply lsubst_aux_allvars_wf_iff in h; rw <- h; clear h.
  pose proof (change_bvars_alpha_spec n vs) as h; simpl in h; repnd.
  applydup @alphaeq_preserves_wf in h; rw h1.
  pose proof (eqvars_free_vars_disjoint_aux
                (change_bvars_alpha vs n)
                (var_ren l f)) as e.
  autodimp e hyp.
  - introv i.
    apply in_var_ren in i; exrepnd; subst; allsimpl.
    rw disjoint_singleton_l; intro k.
    apply Heqf1 in i1; auto.
  - split; intro k; dands; repnd; auto.
    + rw subvars_prop; introv i.
      rw eqvars_prop in e; apply e in i; clear e.
      rw in_app_iff in i.
      rw in_remove_nvars in i.
      dorn i; repnd.
      * rw @dom_sub_var_ren in i; auto.
        applydup @alphaeq_preserves_free_vars in h.
        rw <- h2 in i0.
        rw subvars_prop in k0.
        apply k0 in i0; sp.
      * apply in_sub_free_vars in i; exrepnd.
        apply in_sub_keep_first in i0; repnd.
        apply sub_find_some in i2.
        apply in_var_ren in i2; exrepnd; subst; allsimpl.
        dorn i1; subst; sp.
    + eapply subvars_eqvars in k0;[|exact e]; clear e.
      applydup @alphaeq_preserves_free_vars in h.
      rw <- h2 in k0; clear h2.
      rw subvars_app_l in k0; repnd.
      rw subvars_remove_nvars in k1.
      rw @dom_sub_var_ren in k1; auto.
      rw @free_vars_change_bvars_alpha in Heqf3.
      rw subvars_prop; introv i.
      rw subvars_prop in k1; applydup k1 in i; rw in_app_iff in i0; dorn i0; auto.
      apply Heqf3 in i0; sp.
Qed.

Lemma sosub_prog_change_bvars_in_alpha {o} :
  forall (sub : @SOSub o) vs,
    sosub_prog sub
    <=> sosub_prog (sosub_change_bvars_in_alpha vs sub).
Proof.
  induction sub; introv; split; intro prog; allsimpl; auto;
  destruct a; destruct s;
  allrw @sosub_prog_cons; repnd; dands.
  - apply isprog_vars_change_bvars_alpha; auto.
  - apply IHsub; auto.
  - apply isprog_vars_change_bvars_alpha in prog0; auto.
  - apply IHsub in prog; auto.
Qed.

Lemma sosub_prog_change_bvars_alpha {o} :
  forall (sub : @SOSub o) vs,
    sosub_prog sub
    <=> sosub_prog (sosub_change_bvars_alpha vs sub).
Proof.
  induction sub; introv; split; intro prog; allsimpl; auto;
  destruct a; destruct s;
  allrw @sosub_prog_cons2; repnd; dands.
  - apply isprog_sk_change_bvars_alpha; auto.
  - apply IHsub; auto.
  - apply isprog_sk_change_bvars_alpha in prog0; auto.
  - apply IHsub in prog; auto.
Qed.

Lemma sodom_sosub_change_bvars_in_alpha {o} :
  forall (sub : @SOSub o) vs,
    sodom (sosub_change_bvars_in_alpha vs sub) = sodom sub.
Proof.
  induction sub; simpl; introv; auto.
  destruct a; destruct s.
  unfold sk_change_bvars_alpha.
  rw IHsub; auto.
Qed.

Lemma sodom_sosub_change_bvars_alpha {o} :
  forall (sub : @SOSub o) vs,
    sodom (sosub_change_bvars_alpha vs sub) = sodom sub.
Proof.
  induction sub; simpl; introv; auto.
  destruct a; destruct s.
  rw IHsub; apply eq_cons; auto.
  unfold sk_change_bvars_alpha.
  simpl.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd; sp.
Qed.

Lemma isprogram_sosub1 {p} :
  forall (t : SOTerm) (sub : @SOSub p),
    wf_soterm t
    -> sosub_prog sub
    -> let u := sosub sub t
       in wf_term u
          # subvars
              (free_vars u)
              (sovars2vars (remove_so_vars (sodom sub) (so_free_vars t))).
Proof.
  introv wf prog; simpl.
  unfold sosub.
  boolvar; dands.

  - apply isprogram_sosub_aux1; auto.

  - apply isprogram_sosub_aux1; auto.

  - apply isprogram_sosub_aux1; auto.
    apply sosub_prog_change_bvars_alpha; auto.

  - pose proof (isprogram_sosub_aux1
                  t
                  (sosub_change_bvars_alpha
                     (allvars_range_sosub sub ++ all_fo_vars t) sub))
      as h; simpl in h.
    repeat (autodimp h hyp); auto.
    + apply sosub_prog_change_bvars_alpha; auto.
    + repnd; rw @sodom_sosub_change_bvars_alpha in h; auto.

  - pose proof (isprogram_sosub_aux1
                  (fo_change_bvars_alpha (free_vars_sosub sub ++ all_fo_vars t) [] t)
                  sub) as h.
    repeat (autodimp h hyp).
    + apply wf_soterm_fo_change_bvars_alpha; auto.
    + simpl in h; repnd; auto.

  - pose proof (isprogram_sosub_aux1
                  (fo_change_bvars_alpha (free_vars_sosub sub ++ all_fo_vars t) [] t)
                  sub) as h.
    repeat (autodimp h hyp).
    + apply wf_soterm_fo_change_bvars_alpha; auto.
    + simpl in h; repnd; auto.
      rw @so_free_vars_fo_change_bvars_alpha in h; simpl in h.
      rw map_rename_sovar_nil in h; auto.

  - apply isprogram_sosub_aux1; auto.
    + rw <- @wf_soterm_fo_change_bvars_alpha; auto.
    + apply sosub_prog_change_bvars_alpha; auto.

  - pose proof (isprogram_sosub_aux1
                  (fo_change_bvars_alpha (free_vars_sosub sub ++ all_fo_vars t) [] t)
                  (sosub_change_bvars_alpha
                     (allvars_range_sosub sub
                      ++ all_fo_vars
                           (fo_change_bvars_alpha
                              (free_vars_sosub sub ++ all_fo_vars t) [] t)) sub))
      as h.
    repeat (autodimp h hyp).
    + rw <- @wf_soterm_fo_change_bvars_alpha; auto.
    + apply sosub_prog_change_bvars_alpha; auto.
    + simpl in h; repnd.
      rw @sodom_sosub_change_bvars_alpha in h; auto.
      rw @so_free_vars_fo_change_bvars_alpha in h; simpl in h.
      rw map_rename_sovar_nil in h; auto.
Qed.

Lemma subsovars_cons_l :
  forall v vs1 vs2,
    subsovars (v :: vs1) vs2 <=> LIn v vs2 # subsovars vs1 vs2.
Proof.
  sp; allrw subsovars_eq.
  apply subset_cons_l.
Qed.

Lemma subsovars_app_l :
  forall vs1 vs2 vs,
    subsovars (vs1 ++ vs2) vs <=> (subsovars vs1 vs # subsovars vs2 vs).
Proof.
  introv; allrw subsovars_prop; split; intro k; repnd; dands.
  - introv i; apply k; rw in_app_iff; sp.
  - introv i; apply k; rw in_app_iff; sp.
  - introv i; rw in_app_iff in i; dorn i.
    + apply k0; sp.
    + apply k; sp.
Qed.

Lemma subsovars_app_weak_r1 :
  forall vs1 vs2 vs,
    subsovars vs vs1
    -> subsovars vs (vs1 ++ vs2).
Proof.
  introv sv; allrw subsovars_prop; introv i.
  rw in_app_iff; left; sp.
Qed.

Lemma subsovars_app_weak_r2 :
  forall vs1 vs2 vs,
    subsovars vs vs2
    -> subsovars vs (vs1 ++ vs2).
Proof.
  introv sv; allrw subsovars_prop; introv i.
  rw in_app_iff; right; sp.
Qed.

Lemma remove_so_vars_if_subsovars {o} :
  forall vs (sub : @SOSub o),
    subsovars vs (sodom sub)
    -> remove_so_vars (sodom sub) vs = [].
Proof.
  induction vs; introv sv; allsimpl.
  - rw remove_so_vars_nil_r; auto.
  - rw subsovars_cons_l in sv; repnd.
    rw remove_so_vars_cons_r; boolvar; sp.
Qed.

Lemma isprogram_sosub {o} :
  forall (t : @SOTerm o) sub,
    wf_soterm t
    -> subsovars (so_free_vars t) (sodom sub)
    -> sosub_prog sub
    -> isprogram (sosub sub t).
Proof.
  introv wf sv prog.
  pose proof (isprogram_sosub1 t sub wf prog) as h; simpl in h; repnd.
  rw @remove_so_vars_if_subsovars in h; auto.
  simpl in h; rw subvars_nil_r in h.
  constructor; auto.
  apply nt_wf_eq; auto.
Qed.

Lemma subvars_sovars2vars_prop1 :
  forall vs1 vs2,
    subsovars vs1 vs2
    -> subvars (sovars2vars vs1) (sovars2vars vs2).
Proof.
  introv k.
  rw subvars_prop; introv i.
  allrw in_sovars2vars; exrepnd.
  rw subsovars_prop in k.
  apply k in i0.
  eexists; eauto.
Qed.

Lemma subsovars_remove_so_vars :
  forall vs1 vs2,
    subsovars (remove_so_vars vs1 vs2) vs2.
Proof.
  introv; rw subsovars_prop; introv i.
  rw in_remove_so_vars in i; sp.
Qed.

Lemma sovars2vars_sodom_combine {o} :
  forall (sks : list (@sosub_kind o)) vs,
    length vs = length sks
    -> sovars2vars (sodom (combine vs sks)) = vs.
Proof.
  induction sks; destruct vs; introv len; allsimpl; cpx.
  destruct a; allsimpl.
  apply eq_cons; auto.
Qed.

Definition selectsobt {p} (bts: list SOBTerm) (n:nat) : @SOBTerm p :=
  nth n bts (sobterm [] mk_soaxiom).

Lemma selectbt_map_sosub_b_aux {o} :
  forall (bs : list (@SOBTerm o)) sub n,
    selectbt (map (sosub_b_aux sub) bs) n
    = sosub_b_aux sub (selectsobt bs n).
Proof.
  induction bs; simpl; introv.
  - unfold selectbt, selectsobt; simpl; destruct n; simpl; auto.
  - unfold selectbt, selectsobt; simpl; destruct n; auto.
    apply IHbs.
Qed.

Lemma selectsobt_as_select {o} :
  forall (bs : list (@SOBTerm o)) n,
    n < length bs
    -> Some (selectsobt bs n) = select n bs.
Proof.
  introv h.
  unfold selectsobt.
  rw <- @nth_select1; auto.
Qed.

Definition so_dom {o} (s : @SOSub o) : list NVar :=
  map (fun x => fst x) s.

Definition so_range {o} (s : @SOSub o) : list sosub_kind :=
  map (fun x => snd x) s.

Lemma length_so_dom {o} :
  forall (sub : @SOSub o),
    length (so_dom sub) = length sub.
Proof.
  induction sub; allsimpl; sp.
Qed.

Lemma length_so_range {o} :
  forall (sub : @SOSub o),
    length (so_range sub) = length sub.
Proof.
  induction sub; allsimpl; sp.
Qed.

Lemma sovars2vars_sodom_is_so_dom {o} :
  forall (sub : @SOSub o),
    sovars2vars (sodom sub) = so_dom sub.
Proof.
  induction sub; allsimpl; tcsp.
  destruct a; destruct s; simpl; rw IHsub; auto.
Qed.

Lemma sovars2vars_app :
  forall vs1 vs2,
    sovars2vars (vs1 ++ vs2) = sovars2vars vs1 ++ sovars2vars vs2.
Proof.
  unfold sovars2vars; introv; rw map_app; sp.
Qed.

Lemma sovars2vars_vars2sovars :
  forall vs, sovars2vars (vars2sovars vs) = vs.
Proof.
  induction vs; simpl; auto.
  rw IHvs; sp.
Qed.

Lemma in_vars2sovars :
  forall v n vs,
    LIn (v,n) (vars2sovars vs)
    <=> (LIn v vs # n = 0).
Proof.
  introv; rw in_map_iff; unfold var2sovar; split; intro k; exrepnd; cpx; subst.
  eexists; eauto.
Qed.

Lemma length_vars2sovars :
  forall vs, length (vars2sovars vs) = length vs.
Proof.
  introv; unfold vars2sovars; rw map_length; auto.
Qed.
