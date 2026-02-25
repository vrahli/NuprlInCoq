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

  Authors: Vincent Rahli

*)


Require Export library.
Require Export alphaeq.
Require Export computation3.
Require Export list_tacs.
Require Export substitution2.
Require Export alphaeq2.
Require Export atoms2.


Definition soswapping := list ((NVar # NVar) # nat).

Definition onesoswapvar (a : NVar) (b : NVar) (n : nat) (v : sovar_sig) : sovar_sig :=
  if sovar_sig_dec v (a,n) then (b,n)
  else if sovar_sig_dec v (b,n) then (a,n)
       else v.

Fixpoint soswapvar (l : soswapping) (v : sovar_sig) : sovar_sig :=
  match l with
    | [] => v
    | ((a,b),n) :: rest => soswapvar rest (onesoswapvar a b n v)
  end.

Definition soswapbvars (l : soswapping) (vs : list NVar) :=
  map (fun v => sovar2var (soswapvar l (var2sovar v))) vs.

Fixpoint soswap {p} (l : soswapping) (t : @SOTerm p) :=
  match t with
  | sovar v ts => sovar (sovar2var (soswapvar l (v,length ts))) (map (soswap l) ts)
  | soseq s => soseq s
  | soterm op bts => soterm op (map (soswapbt l) bts)
  end
with soswapbt {p} (l : soswapping) (bt : SOBTerm) :=
       match bt with
       | sobterm vs t => sobterm (soswapbvars l vs) (soswap l t)
       end.


Fixpoint mk_soswapping (vs1 : list sovar_sig) (vs2 : list NVar) : soswapping :=
  match vs1, vs2 with
    | [],[] => []
    | (v1,n) :: vs1, v2 :: vs2 => ((v1,v2),n) :: mk_soswapping vs1 vs2
    | _, _ => []
  end.

Definition matching_sovars (vars1 vars2 : list sovar_sig) :=
  map (fun v => snd v) vars1 = map (fun v => snd v) vars2.

Lemma matching_sovars_sym :
  forall vars1 vars2,
    matching_sovars vars1 vars2 -> matching_sovars vars2 vars1.
Proof.
  unfold matching_sovars; introv e; rw e; auto.
Qed.

Inductive alpha_eq_entry {o} : @library_entry o -> @library_entry o -> Type :=
| aeq_lib_entry :
    forall vs
           opabs
           vars1 rhs1 correct1
           vars2 rhs2 correct2,
      length vs = length vars1
      -> length vs = length vars2
      -> disjoint vs (sovars2vars vars1 ++ sovars2vars vars2 ++ all_fo_vars rhs1 ++ all_fo_vars rhs2)
      -> no_repeats vs
      -> matching_sovars vars1 vars2
      -> so_alphaeq (soswap (mk_soswapping vars1 vs) rhs1)
                    (soswap (mk_soswapping vars2 vs) rhs2)
      -> alpha_eq_entry (lib_abs opabs vars1 rhs1 correct1)
                        (lib_abs opabs vars2 rhs2 correct2).

Inductive alpha_eq_lib {o} : @library o -> @library o -> Type :=
| aeq_lib_nil : alpha_eq_lib [] []
| aeq_lib_cons :
    forall entry1 entry2 lib1 lib2,
      alpha_eq_entry entry1 entry2
      -> alpha_eq_lib lib1 lib2
      -> alpha_eq_lib (entry1 :: lib1) (entry2 :: lib2).

Lemma dom_sub_var_ren {o} :
  forall vs1 vs2,
    length vs1 = length vs2
    -> dom_sub (@var_ren o vs1 vs2) = vs1.
Proof.
  induction vs1; introv len; auto.
  destruct vs2; cpx.
  simpl; apply eq_cons; auto.
  apply IHvs1; auto.
Qed.

Lemma matching_bterms_change_vs {o} :
  forall vars2 vars1 (bs : list (@BTerm o)),
    matching_bterms vars1 bs
    -> matching_sovars vars1 vars2
    -> matching_bterms vars2 bs.
Proof.
  introv m e; allunfold @matching_bterms.
  rw <- m; auto.
Qed.

Lemma matching_entry_change_vs {o} :
  forall vars2 oa1 oa2 vars1 (bs : list (@BTerm o)),
    matching_entry oa1 oa2 vars1 bs
    -> matching_sovars vars1 vars2
    -> matching_entry oa1 oa2 vars2 bs.
Proof.
  introv m e; allunfold @matching_entry; repnd; dands; auto.
  eapply matching_bterms_change_vs; eauto.
Qed.

Lemma found_entry_alpha_eq_lib {o} :
  forall (lib1 lib2 : @library o) oa1 bs oa2 vars rhs correct,
    found_entry lib1 oa1 bs oa2 vars rhs correct
    -> alpha_eq_lib lib1 lib2
    -> {vars2 : list sovar_sig
        & {rhs2 : SOTerm
        & {correct2 : correct_abs oa2 vars2 rhs2
        & {vs : list NVar
        & found_entry lib2 oa1 bs oa2 vars2 rhs2 correct2
        # length vs = length vars
        # length vs = length vars2
        # disjoint vs (sovars2vars vars ++ sovars2vars vars2 ++ all_fo_vars rhs ++ all_fo_vars rhs2)
        # no_repeats vs
        # matching_sovars vars vars2
        # so_alphaeq (soswap (mk_soswapping vars vs) rhs)
                     (soswap (mk_soswapping vars2 vs) rhs2) }}}}.
Proof.
  induction lib1; introv fe aeq.
  - inversion fe.
  - inversion aeq as [|? ? ? ? aeqe aeql]; subst; clear aeq.
    allunfold @found_entry; allsimpl.
    destruct a.
    destruct (matching_entry_deq oa1 opabs vars0 bs).
    + inversion fe; subst.
      assert (correct0 = correct) by eauto with pi; subst; GC.
      inversion aeqe as [? ? ? ? ? ? ? ? len1 len2 disj norep msv aeqb]; subst; GC.
      exists vars2 rhs2 correct2 vs; dands; auto.
      destruct (matching_entry_deq oa1 oa2 vars2 bs); auto.
      apply not_matching_entry_iff in n.
      apply (matching_entry_change_vs vars2) in m; tcsp.
    + eapply IHlib1 in fe; eauto.
      exrepnd.
      inversion aeqe as [? ? ? ? ? ? ? ? len1 len2 disj norep msv aeqb]; subst; GC; clear aeqe.
      exists vars2 rhs2 correct2 vs; dands; auto.
      destruct (matching_entry_deq oa1 opabs vars3 bs); auto.
      apply not_matching_entry_iff in n.
      apply (matching_entry_change_vs vars0) in m; tcsp.
      apply matching_sovars_sym; auto.
Qed.

Lemma matching_bterms_implies_length {o} :
  forall vars (bs : list (@BTerm o)),
    matching_bterms vars bs -> length vars = length bs.
Proof.
   unfold matching_bterms; introv e.
   apply map_eq_length_eq in e; auto.
Qed.

Inductive alphaeq_sosub_range {o} : @SOSub o -> @SOSub o -> Type :=
  | aeqsosub_nil : alphaeq_sosub_range [] []
  | aeqsosub_cons :
      forall v1 v2 sk1 sk2 sub1 sub2,
        alphaeq_sk sk1 sk2
        -> alphaeq_sosub_range sub1 sub2
        -> alphaeq_sosub_range ((v1,sk1) :: sub1) ((v2,sk2) :: sub2).
Hint Constructors alphaeq_sosub_range.

Lemma onesoswapvar_eq :
  forall v1 v2 n,
    onesoswapvar v1 v2 n (v1,n) = (v2,n).
Proof.
  introv; unfold onesoswapvar; boolvar; cpx.
Qed.

Lemma onesoswapvar_not_in :
  forall v1 v2 v n m,
    v1 <> v
    -> v2 <> v
    -> onesoswapvar v1 v2 n (v,m) = (v,m).
Proof.
  introv; unfold onesoswapvar; boolvar; cpx.
Qed.

Lemma onesoswapvar_not_in2 :
  forall v1 v2 v n,
    v <> (v1,n)
    -> v <> (v2,n)
    -> onesoswapvar v1 v2 n v = v.
Proof.
  introv; unfold onesoswapvar; boolvar; cpx.
Qed.

Lemma soswapvar_not_in :
  forall (vs1 : list sovar_sig) (vs2 : list NVar) v n,
    !LIn v (sovars2vars vs1)
    -> !LIn v vs2
    -> soswapvar (mk_soswapping vs1 vs2) (v,n) = (v,n).
Proof.
  induction vs1; destruct vs2; introv ni1 ni2; allsimpl; tcsp; GC.
  - destruct a; simpl; auto.
  - destruct a; allrw not_over_or; repnd; allsimpl.
    rw onesoswapvar_not_in; auto.
Qed.

Lemma soswapvar_not_in2 :
  forall (vs1 : list sovar_sig) (vs2 : list NVar) v,
    !LIn v vs1
    -> !LIn (sovar2var v) vs2
    -> soswapvar (mk_soswapping vs1 vs2) v = v.
Proof.
  induction vs1; destruct vs2; introv ni1 ni2; allsimpl; tcsp; GC.
  - destruct a; simpl; auto.
  - destruct a; allrw not_over_or; repnd; allsimpl.
    destruct v; allsimpl.
    unfold onesoswapvar; boolvar; cpx.
Qed.

Lemma soswapvar_in :
  forall vs1 vs2 v,
    LIn v vs1
    -> length vs1 = length vs2
    -> disjoint vs2 (sovars2vars vs1)
    -> no_repeats vs2
    -> LIn (sovar2var (soswapvar (mk_soswapping vs1 vs2) v)) vs2.
Proof.
  induction vs1; destruct vs2; introv i len disj norep; allsimpl; tcsp.
  destruct a; allsimpl; cpx.
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd.
  allrw no_repeats_cons; repnd.
  allsimpl; allrw not_over_or; repnd.
  dorn i; subst.
  - left.
    rw onesoswapvar_eq.
    rw soswapvar_not_in; simpl; sp.
  - unfold onesoswapvar; destruct v; boolvar; cpx.
    + left; rw soswapvar_not_in; auto.
    + destruct (in_deq sovar_sig sovar_sig_dec (n0,n1) vs1) as [k|k].
      * right; apply IHvs1; auto.
      * provefalse; destruct disj.
        rw in_sovars2vars; eexists; eauto.
Qed.

Lemma length_sodom {o} :
  forall (sub : @SOSub o),
    length (sodom sub) = length sub.
Proof.
  induction sub; allsimpl; sp.
Qed.

Lemma alphaeq_sosub_range_implies_eq_length {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub_range sub1 sub2 -> length sub1 = length sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; auto;
  inversion aeq; subst; sp.
Qed.

Lemma sosub_find_some_eq_sovar2var {o} :
  forall (sub1 sub2 : @SOSub o) v1 v2 sk1 sk2 vs,
    !LIn (sovar2var v1) vs
    -> !LIn (sovar2var v2) vs
    -> disjoint vs (so_dom sub1)
    -> disjoint vs (so_dom sub2)
    -> length vs = length sub1
    -> no_repeats vs
    -> sosub_find sub1 v1 = Some sk1
    -> sosub_find sub2 v2 = Some sk2
    -> sovar2var (soswapvar (mk_soswapping (sodom sub1) vs) v1)
       = sovar2var (soswapvar (mk_soswapping (sodom sub2) vs) v2)
    -> alphaeq_sosub_range sub1 sub2
    -> alphaeq_sk sk1 sk2.
Proof.
  induction sub1; destruct sub2, vs;
  introv ni1 ni2 disj1 disj2 len norep f1 f2 e aeq;
  allsimpl; ginv; GC.
  destruct a, p; destruct s, s0.
  boolvar; allsimpl; subst; cpx;
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd; allsimpl;
  allrw not_over_or; repnd;
  allrw no_repeats_cons; repnd;
  inversion aeq as [|? ? ? ? ? ? aeqsk aeqsub]; subst; auto; clear aeq;
  allrw onesoswapvar_eq.

  - provefalse.

    rw (soswapvar_not_in (sodom sub2) vs n) in e; auto;
    [|rw @sovars2vars_sodom_is_so_dom; complete auto]; allsimpl.

    rw onesoswapvar_not_in2 in e; auto;
    [|destruct v1 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

    pose proof (soswapvar_in (sodom sub1) vs v1) as h.
    destruct sk1, v1.
    apply sosub_find_some in f1; repnd.
    eapply in_sodom_if in f0; eauto;[].
    rewrite f1 in f0.
    repeat (autodimp h hyp);
      [ rw @length_sodom; auto
      | rw @sovars2vars_sodom_is_so_dom; auto
      |].
    rw e in h; sp.

  - provefalse.

    rw (soswapvar_not_in (sodom sub1) vs n) in e; auto;
    [|rw @sovars2vars_sodom_is_so_dom; complete auto]; allsimpl.

    rw onesoswapvar_not_in2 in e; auto;
    [|destruct v2 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

    applydup @alphaeq_sosub_range_implies_eq_length in aeqsub.

    pose proof (soswapvar_in (sodom sub2) vs v2) as h.
    destruct sk2, v2.
    apply sosub_find_some in f2; repnd.
    eapply in_sodom_if in f0; eauto;[].
    rewrite f2 in f0.
    repeat (autodimp h hyp);
      [ rw @length_sodom; auto; lia
      | rw @sovars2vars_sodom_is_so_dom; auto
      |].
    rw <- e in h; sp.

  - rw onesoswapvar_not_in2 in e; auto;
    [|destruct v1 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

    rw onesoswapvar_not_in2 in e; auto;
    [|destruct v2 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

    eapply IHsub1 in e; eauto.
Qed.

Lemma map_nth2 :
  forall (A B : tuniv) d (f : A -> B) (l : list A) (n : nat) b,
    b = f d -> nth n (map f l) b = f (nth n l d).
Proof.
  introv e; subst.
  apply map_nth.
Qed.

Lemma bin_rel_nterm_map {o} :
  forall A (d : A) f1 f2 (l1 l2 : list A) R,
    length l1 = length l2
    -> (forall a1 a2, LIn (a1,a2) (combine l1 l2) -> R (f1 a1) (f2 a2))
    -> f1 d = default_nterm
    -> f2 d = default_nterm
    -> @bin_rel_nterm o R (map f1 l1) (map f2 l2).
Proof.
  introv len imp e1 e2.
  unfold bin_rel_nterm, binrel_list.
  allrw map_length; dands; auto.
  introv i.
  repeat (rewrite (map_nth2 _ _ d); auto).
  apply imp.
  apply in_combine_sel_iff.
  exists n; dands; auto; try lia;
  rw <- @nth_select1; auto; try lia.
Qed.

(* !! MOVE to sovar *)
Lemma fo_bound_vars_subvars_all_fo_vars {o} :
  forall (t : @SOTerm o),
    subvars (fo_bound_vars t) (all_fo_vars t).
Proof.
  soterm_ind t as [v ts ind | | op bs ind] Case; introv; allsimpl; auto.

  - Case "sovar".
    apply subvars_flat_map; introv i.
    applydup ind in i.
    apply subvars_cons_r.
    eapply implies_subvars_flat_map_r; eauto.

  - Case "soterm".
    apply subvars_flat_map; introv i.
    destruct x as [l t]; simpl.
    eapply implies_subvars_flat_map_r; eauto; simpl.
    apply subvars_app_lr; auto.
    eapply ind; eauto.
Qed.

(* !! MOVE to sovar *)
Hint Resolve fovars_subvars_all_fo_vars : slow.

Lemma disjoint_bound_vars_prop4 {o} :
  forall (sub : @SOSub o) v vs t ts,
    disjoint (bound_vars_sosub sub) (free_vars_sosub sub)
    -> disjoint (bound_vars_sosub sub) (flat_map all_fo_vars ts)
    -> LIn (v, sosk vs t) sub
    -> (forall u, LIn u ts -> cover_so_vars u sub)
    -> disjoint (bound_vars t) (flat_map (fun x => free_vars (sosub_aux sub x)) ts).
Proof.
  introv disj1 disj2 insub cov.
  eapply disjoint_bound_vars_prop3; eauto.
  eapply subvars_disjoint_r;[|exact disj2].
  apply subvars_flat_map; introv i.
  eapply implies_subvars_flat_map_r; eauto with slow.
Qed.

Lemma sosub_find_some_none_eq_sovar2var {o} :
  forall (sub1 sub2 : @SOSub o) vs v1 v2 sk,
    !LIn (sovar2var v1) vs
    -> !LIn (sovar2var v2) vs
    -> disjoint vs (so_dom sub1)
    -> length vs = length sub1
    -> no_repeats vs
    -> sosub_find sub1 v1 = Some sk
    -> sosub_find sub2 v2 = None
    -> sovar2var (soswapvar (mk_soswapping (sodom sub1) vs) v1)
       = sovar2var (soswapvar (mk_soswapping (sodom sub2) vs) v2)
    -> False.
Proof.
  induction sub1; destruct sub2, vs;
  introv ni1 ni2 disj len norep f1 f2 e; allsimpl; cpx;
  allrw disjoint_cons_l; allsimpl; repnd;
  allrw disjoint_cons_r; allsimpl; repnd;
  allrw no_repeats_cons; repnd;
  allrw not_over_or; repnd.

  - destruct s; allsimpl; boolvar; ginv; allsimpl.

    + rw onesoswapvar_eq in e.
      rw soswapvar_not_in in e; auto.
      rw @sovars2vars_sodom_is_so_dom; auto.

    + rw onesoswapvar_not_in2 in e; auto;
      [|destruct v1 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

      pose proof (soswapvar_in (sodom sub1) vs v1) as h.
      destruct sk, v1.
      apply sosub_find_some in f1; repnd.
      eapply in_sodom_if in f0; eauto;[].
      rewrite f1 in f0.
      repeat (autodimp h hyp);
        [ rw @length_sodom; auto
        | rw @sovars2vars_sodom_is_so_dom; auto
        |].
      rw e in h; sp.

  - destruct s, s0; allsimpl.
    boolvar; cpx;
    allrw onesoswapvar_eq.

    + rw (soswapvar_not_in (sodom sub1) vs n) in e; auto;
      [|rw @sovars2vars_sodom_is_so_dom; complete auto]; allsimpl.

      rw onesoswapvar_not_in2 in e; auto;
      [|destruct v2 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

      destruct v2 as [x m]; allsimpl.
      apply sosub_find_none in f2.
      rw soswapvar_not_in2 in e; auto.

    + rw onesoswapvar_not_in2 in e; auto;
      [|destruct v1 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

      rw onesoswapvar_not_in2 in e; auto;
      [|destruct v2 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].

      destruct v1 as [x1 m1].
      destruct v2 as [x2 m2].
      allsimpl.
      destruct sk as [lv t].
      apply sosub_find_some in f1; repnd.
      apply sosub_find_none in f2.

      pose proof (soswapvar_in (sodom sub1) vs (x1,m1)) as h.
      eapply in_sodom_if in f0; eauto;[].
      rewrite f1 in f0.
      repeat (autodimp h hyp);
        [ rw @length_sodom; auto
        | rw @sovars2vars_sodom_is_so_dom; auto
        |].
      rw e in h; clear e.

      rw soswapvar_not_in2 in h; auto.
Qed.

Lemma sosub_find_none_eq_sovar2var {o} :
  forall (sub1 sub2 : @SOSub o) vs v1 v2,
    !LIn (sovar2var v1) vs
    -> !LIn (sovar2var v2) vs
    -> length vs = length sub1
    -> sosub_find sub1 v1 = None
    -> sosub_find sub2 v2 = None
    -> sovar2var (soswapvar (mk_soswapping (sodom sub1) vs) v1)
       = sovar2var (soswapvar (mk_soswapping (sodom sub2) vs) v2)
    -> sovar2var v1 = sovar2var v2.
Proof.
  induction sub1; destruct sub2, vs;
  introv ni1 ni2 len f1 f2 e; allsimpl; cpx; GC.

  - destruct p; destruct s; allsimpl; auto.

  - destruct s; allsimpl.
    allrw not_over_or; repnd.
    boolvar; ginv.
    rw onesoswapvar_not_in2 in e; auto;
    [|destruct v1 as [v m]; allsimpl; intro k; inversion k; subst v; complete sp].
    destruct v1 as [x1 m1]; allsimpl.
    apply sosub_find_none in f1.
    rw soswapvar_not_in2 in e; auto.

  - destruct s, s0; allsimpl.
    allrw not_over_or; repnd.
    boolvar; ginv.
    destruct v1 as [x1 m1].
    destruct v2 as [x2 m2].
    allsimpl.

    apply sosub_find_none in f1.
    apply sosub_find_none in f2.

    rw onesoswapvar_not_in2 in e; auto;
    [|intro k; inversion k; subst; complete sp].

    rw onesoswapvar_not_in2 in e; auto;
    [|intro k; inversion k; subst; complete sp].

    rw soswapvar_not_in2 in e; auto.
    rw soswapvar_not_in2 in e; auto.
Qed.

Lemma length_soswapbvars :
  forall s l,
    length (soswapbvars s l) = length l.
Proof.
  induction l; allsimpl; sp.
Qed.

Lemma soswapbvars_nil :
  forall l,
    soswapbvars [] l = l.
Proof.
  induction l; allsimpl; sp.
  f_equal; auto.
Qed.

Lemma length_swap_range_sosub {o} :
  forall sw (sub : @SOSub o),
    length (swap_range_sosub sw sub) = length sub.
Proof.
  induction sub; simpl; sp.
Qed.

Lemma length_cswap_range_sosub {o} :
  forall sw (sub : @SOSub o),
    length (cswap_range_sosub sw sub) = length sub.
Proof.
  induction sub; simpl; sp.
Qed.

Lemma sodom_swap_range_sosub {o} :
  forall sw (sub : @SOSub o),
    sodom (swap_range_sosub sw sub) = sodom sub.
Proof.
  induction sub; simpl; sp.
  destruct a; simpl.
  rw IHsub; rw length_swapbvars; auto.
Qed.

Lemma sodom_cswap_range_sosub {o} :
  forall sw (sub : @SOSub o),
    sodom (cswap_range_sosub sw sub) = sodom sub.
Proof.
  induction sub; simpl; sp.
  destruct a; simpl.
  rw IHsub; rw length_swapbvars; auto.
Qed.

Lemma oneswapvar_eq :
  forall v1 v2, oneswapvar v1 v2 v1 = v2.
Proof.
  introv; unfold oneswapvar; boolvar; sp.
Qed.

Lemma oneswapvar_not_in :
  forall v1 v2 v, v <> v1 -> v <> v2 -> oneswapvar v1 v2 v = v.
Proof.
  introv n1 n2; unfold oneswapvar; boolvar; sp.
Qed.

Lemma in_soswapbvars :
  forall (v : NVar) (sw : soswapping) (vs : list NVar),
    LIn v (soswapbvars sw vs)
    <=> {v' : NVar $ LIn v' vs # v = sovar2var (soswapvar sw (var2sovar v'))}.
Proof.
  introv.
  rw in_map_iff; sp.
Qed.

Lemma in_soswapbvars_implies :
  forall v vs1 vs2 l,
    LIn v (soswapbvars (mk_soswapping vs1 vs2) l)
    -> (LIn v (sovars2vars vs1) [+] LIn v vs2 [+] LIn v l).
Proof.
  induction l; introv i; allsimpl; tcsp.
  dorn i; tcsp.
  clear IHl.
  revert vs2 a v i l.
  induction vs1; introv i; introv; allsimpl.
  - destruct vs2; allsimpl; subst; sp.
  - destruct a; destruct vs2; allsimpl.
    + subst; sp.
    + unfold onesoswapvar in i; boolvar; cpx.
      * unfold var2sovar in e.
        apply pair_inj in e; repnd; subst n0 a0.
        apply IHvs1 with (l := l) in i; auto.
        dorn i; tcsp.
      * unfold var2sovar in e.
        apply pair_inj in e; repnd.
        subst n0 a0.
        apply IHvs1 with (l := l) in i; auto.
        dorn i; tcsp.
      * apply IHvs1 with (l := l) in i; auto.
        dorn i; tcsp.
Qed.

Lemma swapvar_soswapvar :
  forall (vs1 : list sovar_sig) (vs2 l1 l2 : list NVar) v,
    disjoint l2 vs2
    -> disjoint l2 (sovars2vars vs1)
    -> disjoint l2 l1
    -> disjoint vs2 (sovars2vars vs1)
    -> no_repeats vs2
    -> no_repeats l2
    -> !LIn v vs2
    -> !LIn v l2
    -> swapvar (mk_swapping (soswapbvars (mk_soswapping vs1 vs2) l1) l2)
               (sovar2var (soswapvar (mk_soswapping vs1 vs2) (v, 0)))
       = sovar2var
           (soswapvar (mk_soswapping vs1 vs2) (swapvar (mk_swapping l1 l2) v, 0)).
Proof.
  induction l1 as [|x1 l1];
  introv disj1 disj2 disj3 disj4 norep1 norep2 ni1 ni2; allsimpl; auto.
  destruct l2 as [|x2 l2]; allsimpl; auto.
  allrw disjoint_cons_l; repnd.
  allrw disjoint_cons_r; repnd.
  allsimpl.
  allrw no_repeats_cons; repnd.
  allrw not_over_or; repnd.

  destruct (deq_nvar x1 v); subst.

  - repeat (rw oneswapvar_eq).
    rw (swapvar_not_in x2 l1 l2); auto.
    rw soswapvar_not_in; auto; simpl.
    rw swapvar_not_in; auto.
    intro k.
    apply in_soswapbvars_implies in k.
    dorn k;[|dorn k]; tcsp.

  - rw (oneswapvar_not_in x1 x2 v); auto.
    rw <- IHl1; auto; clear IHl1.
    f_equal.
    clear dependent l1.
    clear dependent l2.
    revert dependent v.
    revert dependent x2.
    revert dependent x1.
    revert dependent vs2.
    revert dependent vs1.
    induction vs1; destruct vs2;
    introv norep disj ni1 ni2 ne1 ni3 ne2 ne3;
    allsimpl; GC.
    + rw oneswapvar_not_in; auto.
    + rw oneswapvar_not_in; auto.
    + allrw not_over_or; repnd.
      destruct a; allsimpl.
      rw oneswapvar_not_in; auto.
    + allrw not_over_or; repnd.
      destruct a; allsimpl.
      allrw disjoint_cons_l; allrw disjoint_cons_r; repnd.
      allrw no_repeats_cons; repnd.
      allsimpl; allrw not_over_or; repnd.
      unfold onesoswapvar; boolvar; allunfold var2sovar; cpx.
      * apply IHvs1; sp.
      * apply IHvs1; sp.
        destruct n3; f_equal; sp.
      * apply IHvs1; sp.
        destruct n3; f_equal; sp.
Qed.

Lemma swapbvars_soswapbvars :
  forall l vs1 vs2 l1 l2,
    disjoint l2 vs2
    -> disjoint l2 (sovars2vars vs1)
    -> disjoint l2 l1
    -> disjoint vs2 (sovars2vars vs1)
    -> no_repeats vs2
    -> no_repeats l2
    -> disjoint l vs2
    -> disjoint l l2
    -> swapbvars (mk_swapping (soswapbvars (mk_soswapping vs1 vs2) l1) l2)
                 (soswapbvars (mk_soswapping vs1 vs2) l)
       = soswapbvars (mk_soswapping vs1 vs2) (swapbvars (mk_swapping l1 l2) l).
Proof.
  induction l;
  introv disj1 disj2 disj3 disj4 norep1 norep2 disj5 disj6;
  allsimpl; auto.
  allrw disjoint_cons_l; repnd.
  f_equal.
  - apply swapvar_soswapvar; auto.
  - apply IHl; auto.
Qed.

Lemma so_swap_soswap {o} :
  forall (t : @SOTerm o) (vs1 : list sovar_sig) (vs2 l1 l2 : list NVar),
    disjoint l2 (all_fo_vars t)
    -> disjoint vs2 (all_fo_vars t)
    -> disjoint l2 vs2
    -> disjoint l2 (sovars2vars vs1)
    -> disjoint l2 l1
    -> disjoint vs2 (sovars2vars vs1)
    -> no_repeats vs2
    -> no_repeats l2
    -> so_swap
         (mk_swapping (soswapbvars (mk_soswapping vs1 vs2) l1) l2)
         (soswap (mk_soswapping vs1 vs2) t)
       = soswap (mk_soswapping vs1 vs2) (so_swap (mk_swapping l1 l2) t).
Proof.
  soterm_ind t as [v ts ind | | op bs ind] Case;
  introv disj1 disj2 disj3 disj4 disj5 disj6 norep1 norep2;
  allsimpl; auto.

  - Case "sovar".
    allrw disjoint_cons_r; repnd.
    boolvar; allsimpl; subst; allsimpl; cpx; GC;
    try (complete (allapply map_eq_nil; tcsp));
    allrw map_length; allrw map_map; unfold compose;
    f_equal;
    [|apply eq_maps; introv i; disj_flat_map; apply ind; auto ].

    clear ind.
    apply swapvar_soswapvar; auto.

  - Case "soterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    disj_flat_map.
    allsimpl.
    allrw disjoint_app_r; repnd.
    rw swapbvars_soswapbvars; eauto with slow.
    f_equal.
    eapply ind; eauto.
Qed.

Lemma subvars_swapbvars :
  forall l vs1 vs2 vs,
    disjoint vs2 vs1
    -> no_repeats vs2
    -> disjoint vs2 l
    -> length vs1 = length vs2
    -> subvars l vs
    -> subvars (swapbvars (mk_swapping vs1 vs2) l) (vs2 ++ remove_nvars vs1 vs).
Proof.
  induction l; introv disj1 norep disj2 len sv; allsimpl; auto.
  allrw subvars_cons_l; repnd.
  allrw disjoint_cons_r; repnd.
  dands.

  - destruct (in_deq NVar deq_nvar a vs1).

    + pose proof (swapvar_implies3 vs1 vs2 a) as h.
      repeat (autodimp h hyp); eauto with slow.
      rw in_app_iff; sp.

    + rw swapvar_not_in; auto.
      rw in_app_iff; rw in_remove_nvars; sp.

  - apply IHl; sp.
Qed.

Lemma subvars_fo_bound_vars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    disjoint vs2 vs1
    -> disjoint vs2 (all_fo_vars t)
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> subvars
         (fo_bound_vars (so_swap (mk_swapping vs1 vs2) t))
         (vs2 ++ remove_nvars vs1 (fo_bound_vars t)).
Proof.
  soterm_ind t as [v ts ind | | op bs ind] Case;
  introv disj1 disj2 norep len; allsimpl; auto.

  - Case "sovar".
    allrw disjoint_cons_r; repnd.
    boolvar; subst; allsimpl; auto.
    rw subvars_flat_map; introv i.
    allrw in_map_iff; exrepnd; subst.
    disj_flat_map.
    pose proof (ind a i1 vs1 vs2) as h; repeat (autodimp h hyp).
    eapply subvars_trans;[exact h|].
    apply subvars_app_lr; auto.
    rw subvars_prop; introv k.
    allrw in_remove_nvars; repnd; dands; auto.
    rw lin_flat_map; eexists; eauto.

  - Case "soterm".
    rw flat_map_map; unfold compose.
    apply subvars_flat_map; introv i.
    destruct x as [l t]; simpl.
    disj_flat_map; allsimpl.
    allrw disjoint_app_r; repnd.
    apply subvars_app_l; dands.

    + assert (subvars l (flat_map fo_bound_vars_bterm bs)) as sv.
      { eapply implies_subvars_flat_map_r; eauto.
        simpl; apply subvars_app_weak_l; auto. }

      apply subvars_swapbvars; auto.

    + pose proof (ind t l i vs1 vs2) as h; repeat (autodimp h hyp).
      eapply subvars_trans;[exact h|].
      apply subvars_app_lr; auto.
      rw subvars_prop; introv k.
      allrw in_remove_nvars; repnd; dands; auto.
      rw lin_flat_map.
      exists (sobterm l t); sp.
      simpl.
      rw in_app_iff; sp.
Qed.

Lemma cswap_range_sosub_trivial {o} :
  forall (sub : @SOSub o) vs1 vs2,
    disjoint vs1 (free_vars_sosub sub)
    -> disjoint vs2 (free_vars_sosub sub)
    -> disjoint vs1 (bound_vars_sosub sub)
    -> disjoint vs2 (bound_vars_sosub sub)
    -> disjoint vs1 vs2
    -> no_repeats vs2
    -> cswap_range_sosub (mk_swapping vs1 vs2) sub = sub.
Proof.
  induction sub; introv disj1 disj2 disj3 disj4 disj5 norep; simpl; auto.
  destruct a; allsimpl.
  allrw disjoint_app_r; repnd.
  rw IHsub; auto.
  f_equal; f_equal.
  apply cswapsk_trivial; eauto with slow.
Qed.

Lemma cover_so_vars_so_swap_swap_range_sosub {o} :
  forall (t : @SOTerm o) (vs1 vs2 : list NVar) (sub : SOSub),
    cover_so_vars t sub
    -> cover_so_vars
         (so_swap (mk_swapping vs1 vs2) t)
         (swap_range_sosub (mk_swapping vs1 vs2) sub).
Proof.
  introv cov.
  pose proof (cover_so_vars_so_swap t vs1 vs2 (so_dom sub) (so_range sub)) as h.
  rw <- @swap_range_sosub_combine in h.
  rw <- @sosub_as_combine in h.
  auto.
Qed.

Lemma implies_cover_so_vars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2 sub,
    cover_so_vars t sub
    -> cover_so_vars (so_swap (mk_swapping vs1 vs2) t) sub.
Proof.
  soterm_ind1s t as [ v ts ind | | op lbt ind ] Case; simpl; introv cov; auto.

  - Case "sovar".
    boolvar; subst; allsimpl; auto;
    allrw @cover_so_vars_sovar; repnd; dands; allsimpl; tcsp; introv k.

    + rw null_map in k.
      apply cov0 in k; clear cov0.
      rw map_length; auto.

    + rw in_map_iff in k; exrepnd; subst.
      applydup cov in k1.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm; introv i.
    rw in_map_iff in i; exrepnd.
    destruct a; allsimpl; ginv.
    applydup cov in i1.
    eapply ind; eauto.
Qed.

Lemma alpha_eq_sosub_aux_if_soswap {o} :
  forall (t1 t2 : @SOTerm o) sub1 sub2 vs,
    let vars1 := sodom sub1 in
    let vars2 := sodom sub2 in
    length vs = length vars1
    -> length vs = length vars2
    -> disjoint vs (sovars2vars vars1 ++ sovars2vars vars2 ++ all_fo_vars t1 ++ all_fo_vars t2)
    -> no_repeats vs
    -> disjoint (fo_bound_vars t1) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t1) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t2) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t2) (bound_vars_sosub sub2)
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> alphaeq_sosub_range sub1 sub2
    -> so_alphaeq (soswap (mk_soswapping vars1 vs) t1)
                  (soswap (mk_soswapping vars2 vs) t2)
    -> alpha_eq (sosub_aux sub1 t1) (sosub_aux sub2 t2).
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1 | | op1 bs1 ind1] Case;
  introv len1 len2 disj norep;
  introv disj1 disj2 disj3 disj4 disj5 disj6;
  introv cov1 cov2 aeqsub soaeq;
  allsimpl; auto;
  destruct t2; allsimpl; try (complete (inversion soaeq)).

  - Case "sovar".
    inversion soaeq as [? ? ? len imp x e | |]; subst; clear soaeq.
    allrw map_length.
    allrw disjoint_app_r.
    allrw disjoint_cons_r.
    allrw disjoint_app_r.
    allrw disjoint_cons_r.
    repnd.

    allrw @sovars2vars_sodom_is_so_dom.
    allrw @length_sodom.
    allrw @cover_so_vars_sovar; repnd.

    remember (sosub_find sub1 (v1, length ts1)) as f1; symmetry in Heqf1; destruct f1;
    remember (sosub_find sub2 (n, length l)) as g1; symmetry in Heqg1; destruct g1;
    try (destruct s); try (destruct s0).

    + pose proof (sosub_find_some_eq_sovar2var
                    sub1 sub2 (v1,length ts1) (n,length l)
                    (sosk l0 n0) (sosk l1 n1) vs) as h; allsimpl.
      repeat (autodimp h hyp); try lia.

      apply alphaeq_sk_iff_alphaeq_bterm2 in h; simpl in h.

      pose proof (apply_bterm_alpha_congr
                    (bterm l0 n0) (bterm l1 n1)
                    (map (sosub_aux sub1) ts1)
                    (map (sosub_aux sub2) l)) as k.
      repeat (autodimp k hyp).

      * apply (bin_rel_nterm_map _ default_soterm); auto.
        introv i.
        applydup in_combine in i; repnd.
        allrw disjoint_cons_l; repnd.
        disj_flat_map.
        pose proof (fo_bound_vars_subvars_all_fo_vars a1) as sv1.
        pose proof (fo_bound_vars_subvars_all_fo_vars a2) as sv2.
        apply ind1 with (vs := vs); auto;
        allrw @length_sodom; allrw @sovars2vars_sodom_is_so_dom; auto.

        { allrw disjoint_app_r; dands; auto. }

        { apply imp.
          rw <- @map_combine.
          rw in_map_iff.
          exists (a1,a2); dands; auto. }

      * allrw map_length.
        unfold num_bvars; simpl.
        apply sosub_find_some in Heqf1; sp.

      * unfold apply_bterm in k; simpl in k.
        applydup @sosub_find_some in Heqf1; repnd.
        applydup @sosub_find_some in Heqg1; repnd.
        revert k.
        change_to_lsubst_aux4; tcsp;
        rw flat_map_map; unfold compose;
        eapply disjoint_bound_vars_prop4; eauto with slow.

    + pose proof (sosub_find_some_none_eq_sovar2var
                    sub1 sub2 vs
                    (v1, length ts1) (n, length l)
                    (sosk l0 n0)) as h.
      repeat (autodimp h hyp); sp.

    + pose proof (sosub_find_some_none_eq_sovar2var
                    sub2 sub1 vs
                    (n, length l) (v1, length ts1)
                    (sosk l0 n0)) as h.
      repeat (autodimp h hyp); sp.

    + pose proof (sosub_find_none_eq_sovar2var
                    sub1 sub2 vs (v1, length ts1) (n, length l)) as h.
      repeat (autodimp h hyp); sp.
      allsimpl; subst.

      apply alphaeq_eq.
      apply alphaeq_apply_list; eauto with slow.

      apply (bin_rel_nterm_map _ default_soterm); auto.
      introv i.
      applydup in_combine in i; repnd.
      allrw disjoint_cons_l; repnd.
      disj_flat_map.
      pose proof (fo_bound_vars_subvars_all_fo_vars a1) as sv1.
      pose proof (fo_bound_vars_subvars_all_fo_vars a2) as sv2.
      apply ind1 with (vs := vs); auto;
      allrw @length_sodom; allrw @sovars2vars_sodom_is_so_dom; auto.

      { allrw disjoint_app_r; dands; auto. }

      { apply imp.
        rw <- @map_combine.
        rw in_map_iff.
        exists (a1,a2); dands; auto. }

  - Case "soseq".
    inversion soaeq as [ | ? ? F | ]; clear soaeq; subst; allsimpl; tcsp.
    constructor; introv; apply alphaeq_eq; apply F.

  - Case "soterm".

    allrw @cover_so_vars_soterm.
    allrw disjoint_app_r; repnd.
    allrw @sovars2vars_sodom_is_so_dom.
    allrw @length_sodom.

    inversion soaeq as [ | | ? ? ? len imp]; subst; clear soaeq.
    allrw map_length.

    apply alpha_eq_oterm_combine; allrw map_length; dands; auto;[].

    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd; allsimpl; cpx.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2].
    simpl.

    applydup in_combine in i1; repnd.
    applydup cov1 in i2.
    applydup cov2 in i0.

    pose proof (imp
                  (soswapbt (mk_soswapping (sodom sub1) vs) (sobterm l1 t1))
                  (soswapbt (mk_soswapping (sodom sub2) vs) (sobterm l2 t2)))
      as soaeqb.
    autodimp soaeqb hyp;[rw <- @map_combine; rw in_map_iff; eexists; complete eauto|].
    simpl in soaeqb.
    apply (so_alphaeqbt_vs_implies_more
             _ _ _ (vs
                      ++ l1
                      ++ l2
                      ++ all_fo_vars t1
                      ++ all_fo_vars t2
                      ++ sovars2vars (sodom sub1)
                      ++ sovars2vars (sodom sub2)
                      ++ allvars (sosub_aux (sosub_filter sub1 (vars2sovars l1)) t1)
                      ++ allvars (sosub_aux (sosub_filter sub2 (vars2sovars l2)) t2)
                      ++ get_fo_vars (sodom (sosub_filter sub1 (vars2sovars l1)))
                      ++ get_fo_vars (sodom (sosub_filter sub2 (vars2sovars l2)))
                      ++ free_vars_sosub sub1
                      ++ bound_vars_sosub sub1
                      ++ free_vars_sosub sub2
                      ++ bound_vars_sosub sub2
          )) in soaeqb; auto.
    (* vs0 can be disjoint from whatever we want using so_alphaeq_vs_implies_more *)
    inversion soaeqb as [? ? ? ? ? el1 el2 d nr soaeq]; subst; allsimpl; clear soaeqb.
    allrw disjoint_app_r; repnd.
    allrw length_soswapbvars.

    disj_flat_map.
    allsimpl; allrw disjoint_app_r; allrw disjoint_app_l; repnd.

    pose proof (so_swap_soswap t1 (sodom sub1) vs l1 vs0)
      as e1.
    repeat (autodimp e1 hyp); allrw @sovars2vars_sodom_is_so_dom; auto.

    pose proof (so_swap_soswap t2 (sodom sub2) vs l2 vs0)
      as e2.
    repeat (autodimp e2 hyp); allrw @sovars2vars_sodom_is_so_dom; auto.

    rw e1 in soaeq.
    rw e2 in soaeq.

    apply (so_alphaeq_vs_implies_less _ _ _ []) in soaeq; auto.

    apply alphaeqbt_eq.
    apply (aeqbt _ vs0); auto; try lia.

    { allrw disjoint_app_r; sp. }

    pose proof (sosub_aux_cswap_cswap3
                  t1 (sosub_filter sub1 (vars2sovars l1))
                  l1 vs0) as h1.
    repeat (autodimp h1 hyp).
    { rw disjoint_app_r; sp. }
    { rw @sodom_sosub_filter.
      rw get_fo_vars_remove_so_vars.
      apply disjoint_remove_nvars_l.
      rw remove_nvars_eq; auto. }
    { apply cover_so_vars_sosub_filter; auto. }

    pose proof (sosub_aux_cswap_cswap3
                  t2 (sosub_filter sub2 (vars2sovars l2))
                  l2 vs0) as h2.
    repeat (autodimp h2 hyp).
    { rw disjoint_app_r; sp. }
    { rw @sodom_sosub_filter.
      rw get_fo_vars_remove_so_vars.
      apply disjoint_remove_nvars_l.
      rw remove_nvars_eq; auto. }
    { apply cover_so_vars_sosub_filter; auto. }

    rw h1; rw h2.
    clear h1 h2.

    repeat (rw <- @sosub_filter_cswap_range_sosub; auto).
    repeat (rw @sosub_aux_sosub_filter; auto);
      try (complete (apply disjoint_fovars_so_swap; eauto with slow; try lia)).

    pose proof (ind1
                  t1
                  (so_swap (mk_swapping l1 vs0) t1)
                  l1
                  i2
                  (sosize_so_swap_le t1 (mk_swapping l1 vs0))
                  (so_swap (mk_swapping l2 vs0) t2)
                  (cswap_range_sosub (mk_swapping l1 vs0) sub1)
                  (cswap_range_sosub (mk_swapping l2 vs0) sub2)
                  vs
               ) as h.
    allrw @length_sodom.
    allrw @length_cswap_range_sosub.
    allrw @sodom_cswap_range_sosub.
    allrw @sovars2vars_sodom_is_so_dom.
    repeat (rw @cswap_range_sosub_trivial in h; eauto with slow).
    repeat (rw @cswap_range_sosub_trivial; eauto with slow).

    repeat (autodimp h hyp); try lia.

    { allrw disjoint_app_r; dands; eauto 3 with slow.
      - apply disjoint_all_fo_vars_so_swap; eauto 3 with slow.
      - apply disjoint_all_fo_vars_so_swap; eauto 3 with slow. }

    { pose proof (subvars_fo_bound_vars_so_swap t1 l1 vs0) as sv1.
      repeat (autodimp sv1 hyp).
      eapply subvars_disjoint_l;[exact sv1|].
      apply disjoint_app_l; dands; eauto 4 with slow. }

    { apply disjoint_sym.
      apply disjoint_all_fo_vars_so_swap; eauto 3 with slow. }

    { pose proof (subvars_fo_bound_vars_so_swap t2 l2 vs0) as sv1.
      repeat (autodimp sv1 hyp).
      eapply subvars_disjoint_l;[exact sv1|].
      apply disjoint_app_l; dands; eauto 4 with slow. }

    { apply disjoint_sym.
      apply disjoint_all_fo_vars_so_swap; eauto 3 with slow. }

    { apply implies_cover_so_vars_so_swap; auto. }

    { apply implies_cover_so_vars_so_swap; auto. }

    { apply alphaeq_eq; auto. }
Qed.

Lemma sovar2var_soswapvar_more :
  forall vs1 vs2 vs vs' v1 v2 n1 n2,
    disjoint vs (sovars2vars vs1)
    -> disjoint vs (sovars2vars vs2)
    -> no_repeats vs
    -> !LIn v1 vs
    -> !LIn v2 vs
    -> disjoint vs' (sovars2vars vs1)
    -> disjoint vs' (sovars2vars vs2)
    -> no_repeats vs'
    -> !LIn v1 vs'
    -> !LIn v2 vs'
    -> length vs1 = length vs
    -> length vs2 = length vs
    -> length vs' = length vs
    -> sovar2var (soswapvar (mk_soswapping vs1 vs) (v1, n1))
       = sovar2var (soswapvar (mk_soswapping vs2 vs) (v2, n2))
    -> sovar2var (soswapvar (mk_soswapping vs1 vs') (v1, n1))
       = sovar2var (soswapvar (mk_soswapping vs2 vs') (v2, n2)).
Proof.
  induction vs1;
  introv disj1 disj2 norep1 ni1 ni2;
  introv disj3 disj4 norep2 ni3 ni4;
  introv len1 len2 len3 e; allsimpl.
  - destruct vs; allsimpl; cpx.
  - destruct a.
    destruct vs; allsimpl; cpx.
    destruct vs'; allsimpl; cpx.
    destruct vs2; allsimpl; cpx.
    destruct s; allsimpl.
    allrw disjoint_cons_l; allrw disjoint_cons_r; allsimpl; repnd.
    allrw not_over_or; repnd.
    allrw no_repeats_cons; repnd.
    allunfold onesoswapvar; boolvar; auto; cpx.
    + rw soswapvar_not_in; auto.
      rw soswapvar_not_in; auto.
    + provefalse.
      rw soswapvar_not_in in e; auto; allsimpl.
      pose proof (in_deq sovar_sig sovar_sig_dec (v2,n2) vs2) as [i|i].
      * pose proof (soswapvar_in vs2 vs (v2,n2)) as h.
        repeat (autodimp h hyp).
        rw <- e in h; sp.
      * rw soswapvar_not_in2 in e; sp.
    + provefalse.
      rw (soswapvar_not_in vs2 vs) in e; auto; allsimpl.
      pose proof (in_deq sovar_sig sovar_sig_dec (v1,n1) vs1) as [i|i].
      * pose proof (soswapvar_in vs1 vs (v1,n1)) as h.
        repeat (autodimp h hyp).
        rw e in h; sp.
      * rw soswapvar_not_in2 in e; sp.
    + eapply IHvs1; eauto; try lia.
Qed.

Lemma so_alphaeq_soswap_more {o} :
  forall (t1 t2 : @SOTerm o) vs1 vs2 vs vs',
    disjoint vs (sovars2vars vs1)
    -> disjoint vs (sovars2vars vs2)
    -> disjoint vs (all_fo_vars t1)
    -> disjoint vs (all_fo_vars t2)
    -> no_repeats vs
    -> disjoint vs' (sovars2vars vs1)
    -> disjoint vs' (sovars2vars vs2)
    -> disjoint vs' (all_fo_vars t1)
    -> disjoint vs' (all_fo_vars t2)
    -> no_repeats vs'
    -> length vs1 = length vs
    -> length vs2 = length vs
    -> length vs' = length vs
    -> so_alphaeq (soswap (mk_soswapping vs1 vs) t1)
                  (soswap (mk_soswapping vs2 vs) t2)
    -> so_alphaeq (soswap (mk_soswapping vs1 vs') t1)
                  (soswap (mk_soswapping vs2 vs') t2).
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1 | | op1 bs1 ind1] Case;
  introv disj1 disj2 disj3 disj4 norep1;
  introv disj5 disj6 disj7 disj8 norep2;
  introv len1 len2 len3 aeq;
  allsimpl.

  - Case "sovar".
    destruct t2 as [v2 ts2 | | op2 bs2]; allsimpl;
    try (complete (inversion aeq)).
    allrw disjoint_cons_r; repnd.
    inversion aeq as [? ? ? len imp x e | |]; subst; clear aeq.
    allrw map_length.
    pose proof (sovar2var_soswapvar_more vs1 vs2 vs vs' v1 v2 (length ts1) (length ts2)) as h.
    repeat (autodimp h hyp).
    rw h.
    constructor.
    + allrw map_length; auto.
    + introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; allsimpl; cpx.
      applydup in_combine in i1; repnd.
      disj_flat_map.
      apply ind1 with (vs := vs); auto; try lia.
      apply imp.
      rw <- @map_combine.
      apply in_map_iff.
      exists (a0,a); simpl; sp.

  - Case "soseq".
    inversion aeq as [ | ? ? F | ]; clear aeq; subst; allsimpl; tcsp.
    destruct t2 as [v|s'|op bs]; allsimpl; ginv.
    constructor; introv; apply F.

  - Case "soterm".
    destruct t2 as [| |op2 bs2]; try (complete (inversion aeq)).
    inversion aeq as [| |? ? ? len imp x]; subst; clear aeq.
    allrw map_length; allsimpl.
    constructor; allrw map_length; auto.

    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2].
    cpx.
    applydup in_combine in i1; repnd.
    disj_flat_map.
    allsimpl; allrw disjoint_app_r; repnd.

    pose proof (imp (soswapbt (mk_soswapping vs1 vs) (sobterm l1 t1))
                    (soswapbt (mk_soswapping vs2 vs) (sobterm l2 t2))) as h.
    autodimp h hyp.
    { rw <- @map_combine; rw in_map_iff; eexists; eauto. }

    simpl in h.
    apply (so_alphaeqbt_vs_implies_more
             _ _ _ (vs
                      ++ vs'
                      ++ l1
                      ++ l2
                      ++ all_fo_vars t1
                      ++ all_fo_vars t2
                      ++ soswapbvars (mk_soswapping vs1 vs') l1
                      ++ soswapbvars (mk_soswapping vs2 vs') l2
                      ++ all_fo_vars (soswap (mk_soswapping vs1 vs') t1)
                      ++ all_fo_vars (soswap (mk_soswapping vs2 vs') t2)
                      ++ sovars2vars vs1
                      ++ sovars2vars vs2
          )) in h; auto.
    inversion h as [? ? ? ? ? el1 el2 disj norep aeq]; subst; allsimpl; clear h.
    allrw disjoint_app_r; repnd.
    apply (so_alphaeq_vs_implies_less _ _ _ []) in aeq; auto.
    apply (soaeqbt _ vs0); allsimpl; allrw length_soswapbvars; auto.

    { allrw disjoint_app_r; dands; eauto with slow. }

    pose proof (so_swap_soswap t1 vs1 vs' l1 vs0) as e1.
    repeat (autodimp e1 hyp).

    pose proof (so_swap_soswap t2 vs2 vs' l2 vs0) as e2.
    repeat (autodimp e2 hyp).

    rw e1; rw e2; clear e1 e2.

    pose proof (so_swap_soswap t1 vs1 vs l1 vs0) as e1.
    repeat (autodimp e1 hyp).

    pose proof (so_swap_soswap t2 vs2 vs l2 vs0) as e2.
    repeat (autodimp e2 hyp).

    rw e1 in aeq; rw e2 in aeq; clear e1 e2.

    pose proof (ind1
                  t1
                  (so_swap (mk_swapping l1 vs0) t1)
                  l1
                  i2
                  (sosize_so_swap_le t1 (mk_swapping l1 vs0))
                  (so_swap (mk_swapping l2 vs0) t2)
                  vs1 vs2
                  vs vs'
               ) as h.
    repeat (autodimp h hyp).

    { apply disjoint_all_fo_vars_so_swap; eauto with slow. }

    { apply disjoint_all_fo_vars_so_swap; eauto with slow. }

    { apply disjoint_all_fo_vars_so_swap; eauto with slow. }

    { apply disjoint_all_fo_vars_so_swap; eauto with slow. }
Qed.

Lemma alphaeq_sosub_implies_alphaeq_sosub_range {o} :
    forall (sub1 sub2 : @SOSub o),
      alphaeq_sosub sub1 sub2
      -> alphaeq_sosub_range sub1 sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; auto;
  inversion aeq; subst.
  constructor; auto.
Qed.
Hint Resolve alphaeq_sosub_implies_alphaeq_sosub_range : slow.

Lemma alphaeq_sosub_range_trans {o} :
  forall (sub1 sub2 sub3 : @SOSub o),
    alphaeq_sosub_range sub1 sub2
    -> alphaeq_sosub_range sub2 sub3
    -> alphaeq_sosub_range sub1 sub3.
Proof.
  induction sub1; destruct sub2, sub3; introv aeq1 aeq2; tcsp;
  inversion aeq1; inversion aeq2; subst; cpx; clear aeq1 aeq2.
  constructor; eauto.
  eapply alphaeq_sk_trans; eauto.
Qed.
Hint Resolve alphaeq_sosub_range_trans : slow.

Lemma alphaeq_sosub_range_sym {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub_range sub1 sub2
    -> alphaeq_sosub_range sub2 sub1.
Proof.
  induction sub1; destruct sub2; introv aeq; tcsp;
  inversion aeq; subst; cpx; clear aeq.
  constructor; eauto.
  eapply alphaeq_sk_sym; eauto.
Qed.
Hint Resolve alphaeq_sosub_range_sym : slow.

Lemma alphaeq_sosub_range_refl {o} :
  forall (sub :@SOSub o),
    alphaeq_sosub_range sub sub.
Proof.
  induction sub; auto.
  destruct a.
  constructor; auto.
  apply alphaeq_sk_refl.
Qed.
Hint Resolve alphaeq_sosub_range_refl : slow.

Lemma so_alphaeq_soswap {o} :
  forall (t1 t2 : @SOTerm o) vs1 vs2,
    disjoint vs2 (all_fo_vars t1)
    -> disjoint vs2 (all_fo_vars t2)
    -> disjoint vs2 (sovars2vars vs1)
    -> no_repeats vs2
    -> so_alphaeq t1 t2
    -> so_alphaeq (soswap (mk_soswapping vs1 vs2) t1)
                  (soswap (mk_soswapping vs1 vs2) t2).
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1| |op1 bs1 ind1] Case;
  introv disj1 disj2 disj3 norep aeq; allsimpl;
  destruct t2 as [v2 ts2 | |op2 bs2];
  inversion aeq as [? ? ? len imp | ? ? F |? ? ? len imp]; subst; clear aeq;
  allsimpl.

  - Case "sovar".
    rw len.
    constructor; allrw map_length; auto.
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
    applydup in_combine in i1; repnd.
    allrw disjoint_cons_r; repnd.
    disj_flat_map.
    apply ind1; auto.
    apply imp; auto.

  - Case "soseq".
    constructor; auto.

  - Case "soterm".
    constructor; allrw map_length; auto.
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2].
    applydup in_combine in i1; repnd.
    allsimpl.
    applydup imp in i1.

    apply (so_alphaeqbt_vs_implies_more
             _ _ _ (soswapbvars (mk_soswapping vs1 vs2) l1
                                ++ soswapbvars (mk_soswapping vs1 vs2) l2
                                ++ all_fo_vars (soswap (mk_soswapping vs1 vs2) t1)
                                ++ all_fo_vars (soswap (mk_soswapping vs1 vs2) t2)
                                ++ all_fo_vars t1
                                ++ all_fo_vars t2
                                ++ vs2
                                ++ sovars2vars vs1
          )) in i3; auto.
    inversion i3 as [? ? ? ? ? el1 el2 disj norep2 aeq]; subst; allsimpl; clear i3.
    allrw disjoint_app_r; repnd.
    apply (so_alphaeq_vs_implies_less _ _ _ []) in aeq; auto.

    apply (soaeqbt _ vs); allrw length_soswapbvars; allsimpl; auto; try lia.

    { allrw disjoint_app_r; dands; eauto with slow. }

    disj_flat_map.
    allsimpl.
    allrw disjoint_app_r; repnd.

    pose proof (so_swap_soswap t1 vs1 vs2 l1 vs) as e1.
    repeat (autodimp e1 hyp).

    pose proof (so_swap_soswap t2 vs1 vs2 l2 vs) as e2.
    repeat (autodimp e2 hyp).

    rw e1; rw e2; clear e1 e2.

    pose proof (ind1
                  t1
                  (so_swap (mk_swapping l1 vs) t1)
                  l1
                  i2
                  (sosize_so_swap_le t1 (mk_swapping l1 vs))
                  (so_swap (mk_swapping l2 vs) t2)
                  vs1 vs2
               ) as h.
    repeat (autodimp h hyp).

    apply disjoint_all_fo_vars_so_swap; eauto with slow.

    apply disjoint_all_fo_vars_so_swap; eauto with slow.
Qed.

Lemma alpha_eq_sosub_if_soswap {o} :
  forall vs (t1 t2 : @SOTerm o) sub1 sub2,
    let vars1 := sodom sub1 in
    let vars2 := sodom sub2 in
    length vs = length vars1
    -> length vs = length vars2
    -> disjoint vs (sovars2vars vars1 ++ sovars2vars vars2 ++ all_fo_vars t1 ++ all_fo_vars t2)
    -> no_repeats vs
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> alphaeq_sosub_range sub1 sub2
    -> so_alphaeq (soswap (mk_soswapping vars1 vs) t1)
                  (soswap (mk_soswapping vars2 vs) t2)
    -> alpha_eq (sosub sub1 t1) (sosub sub2 t2).
Proof.
  introv len1 len2 disj norep cov1 cov2 aeqsub soaeq.
  pose proof (unfold_sosub sub1 t1) as h1.
  pose proof (unfold_sosub sub2 t2) as k1.
  destruct h1 as [sub1' h1].
  destruct h1 as [t1' h1]; repnd.
  destruct k1 as [sub2' k1].
  destruct k1 as [t2' k1]; repnd.
  rw h1; rw k1.

  applydup @alphaeq_sosub_implies_eq_lengths in h0.
  applydup @alphaeq_sosub_implies_eq_lengths in k0.

  pose proof (cover_so_vars_if_so_alphaeq t1 t1' sub1 cov1 h2) as cov1'.
  pose proof (cover_so_vars_if_alphaeq_sosub t1' sub1 sub1' cov1' h0) as cov1''.

  pose proof (cover_so_vars_if_so_alphaeq t2 t2' sub2 cov2 k2) as cov2'.
  pose proof (cover_so_vars_if_alphaeq_sosub t2' sub2 sub2' cov2' k0) as cov2''.

  pose proof (fresh_vars
                (length vs)
                (vs
                   ++ sovars2vars (sodom sub1)
                   ++ sovars2vars (sodom sub2)
                   ++ all_fo_vars t1
                   ++ all_fo_vars t2
                   ++ all_fo_vars t1'
                   ++ all_fo_vars t2'
             )) as fv.
  exrepnd.
  allrw disjoint_app_r; repnd.

  pose proof (so_alphaeq_soswap_more t1 t2 (sodom sub1) (sodom sub2) vs lvn) as h.
  repeat (autodimp h hyp).

  pose proof (alphaeq_sosub_implies_eq_sodoms sub1 sub1' h0) as ed1.
  applydup @eq_sodoms_implies_eq_so_doms in ed1 as ed1'.
  pose proof (alphaeq_sosub_implies_eq_sodoms sub2 sub2' k0) as ed2.
  applydup @eq_sodoms_implies_eq_so_doms in ed2 as ed2'.

  apply (alpha_eq_sosub_aux_if_soswap _ _ _ _ lvn);
    eauto;
    allrw @length_sodom; auto; try lia;
    allrw @sovars2vars_sodom_is_so_dom.

  { allrw disjoint_app_r.
    rw <- ed1'.
    rw <- ed2'.
    dands; auto. }

  { allapply @alphaeq_sosub_implies_alphaeq_sosub_range.
    eauto with slow. }

  { rw <- ed1.
    rw <- ed2.
    apply (so_alphaeq_soswap _ _ (sodom sub1) lvn) in h2; auto;
    allrw @sovars2vars_sodom_is_so_dom; auto.
    apply (so_alphaeq_soswap _ _ (sodom sub2) lvn) in k2; auto;
    allrw @sovars2vars_sodom_is_so_dom; auto.
    eauto with slow. }
Qed.

Lemma matching_sovars_cons :
  forall v1 v2 vs1 vs2,
    matching_sovars (v1 :: vs1) (v2 :: vs2)
    <=> (snd v1 = snd v2 # matching_sovars vs1 vs2).
Proof.
  introv; unfold matching_sovars; simpl; split; intro k; cpx; repnd.
  f_equal; auto.
Qed.

Lemma alphaeq_sosub_range_mk_abs_subst {o} :
  forall vars1 vars2 (bs : list (@BTerm o)),
    matching_bterms vars1 bs
    -> matching_bterms vars2 bs
    -> matching_sovars vars1 vars2
    -> alphaeq_sosub_range (mk_abs_subst vars1 bs) (mk_abs_subst vars2 bs).
Proof.
  induction vars1; destruct vars2, bs; introv m1 m2 m; allsimpl; tcsp;
  try (complete (inversion m));
  try (complete (inversion m1));
  try (complete (inversion m2)).

  destruct a, s.
  destruct b; allsimpl.
  allrw @matching_bterms_cons; repnd; allsimpl; subst.
  allunfold @num_bvars; allsimpl.
  allrw matching_sovars_cons; allsimpl; repnd.
  boolvar; auto.
  constructor; auto.
  apply alphaeq_sk_refl.
Qed.

Lemma alpha_eq_mk_abs_subst_if_bterm {o} :
  forall vs vars1 vars2 (t1 t2 : @SOTerm o) bs,
    matching_bterms vars1 bs
    -> matching_bterms vars2 bs
    -> length vs = length vars1
    -> length vs = length vars2
    -> disjoint vs (sovars2vars vars1 ++ sovars2vars vars2 ++ all_fo_vars t1 ++ all_fo_vars t2)
    -> no_repeats vs
    -> matching_sovars vars1 vars2
    -> socovered t1 vars1
    -> socovered t2 vars2
    -> so_alphaeq (soswap (mk_soswapping vars1 vs) t1)
                  (soswap (mk_soswapping vars2 vs) t2)
    -> alpha_eq (mk_instance vars1 bs t1)
                (mk_instance vars2 bs t2).
Proof.
  introv m1 m2 len1 len2 disj norep msv cov1 cov2 aeq.
  unfold mk_instance.
  apply (alpha_eq_sosub_if_soswap vs); auto;
  try (complete (allrw <- @mk_abs_subst_some_prop2; auto));
  try (complete (apply socovered_implies_cover_so_vars; auto)).
  apply alphaeq_sosub_range_mk_abs_subst; auto.
Qed.

Lemma eapply_wf_def_lam {o} :
  forall v (b : @NTerm o), eapply_wf_def (mk_lam v b).
Proof.
  introv; right; right; eexists; eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_lam : slow.

Lemma eapply_wf_def_nseq {o} :
  forall (s : nseq), @eapply_wf_def o (mk_nseq s).
Proof.
  introv; right; left; eexists; eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_nseq : slow.

Lemma compute_step_alpha_lib {p} :
  forall lib1 lib2 t1 t2,
    alpha_eq_lib lib1 lib2
    -> compute_step lib1 t1 = csuccess t2
    -> {t2' : @NTerm p
        & compute_step lib2 t1 = csuccess t2'
        # alpha_eq t2 t2'}.
Proof.
  nterm_ind1s t1 as [v1|f1|o1 lbt1 IHind] Case; introv Hal Hcomp;
  duplicate Hal as backup;
  [ subst;
    invertsn Hal;
    invertsn Hcomp
  | |].

  { Case "sterm".
    csunf Hcomp; allsimpl; ginv.
    csunf; simpl.
    exists (sterm f1); dands; eauto. }

  Case "oterm".
  dopid o1 as [c1 | nc1 | exc1 | abs1] SCase.

  - SCase "Can".
    inverts Hcomp; auto.
    exists (oterm (Can c1) lbt1); simpl; auto.

  - SCase "NCan".  (* destruct lbt and the bts inside enough
    times so that the structure re4quired
     for computation rules is visible. need to split
      on whether the opid of arg1(prin_arg) is canonical *)

    dlist lbt1 SSCase as [| arg1];
      [ dopid_noncan nc1 SSSCase;
        inverts Hcomp
      |
      ]; [].
    (*takes care of nilcase as no ncop takes 0 bterms*)

    SSCase "conscase".
    destruct arg1 as [arg1vs arg1nt];
      dlist arg1vs SSSCase as [|arg1v1].

    {
    SSSCase "nilcase".
    destruct arg1nt as [v89|f| arg1o arg1bts];
      [inverts Hcomp| |];
      [|].

    { csunf Hcomp; allsimpl.
      dopid_noncan nc1 SSSSCase; allsimpl; ginv.

      - SSSSCase "NApply".
        apply compute_step_seq_apply_success in Hcomp; exrepnd; subst.
        csunf; simpl; eexists; dands; eauto.

      - SSSSCase "NEApply".
        apply compute_step_eapply_success in Hcomp; exrepnd; subst.
        repndors; exrepnd; subst; allsimpl.

        + apply compute_step_eapply2_success in Hcomp1; repnd; subst.
          repndors; exrepnd; ginv.
          csunf; simpl.
          dcwf h; simpl.
          boolvar; try lia.
          rw Znat.Nat2Z.id; eexists; dands; eauto.

        + fold_terms; unfold mk_eapply.
          rw @compute_step_eapply_iscan_isexc; eauto 3 with slow.

        + pose proof (IHind arg2 arg2 []) as h; clear IHind.
          repeat (autodimp h hyp); eauto 3 with slow.
          pose proof (h x) as ih; clear h.
          repeat (autodimp ih hyp); exrepnd.
          fold_terms; unfold mk_eapply.
          rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
          rw ih1; eexists; dands; eauto.
          prove_alpha_eq2.

      - SSSSCase "NFix".
        apply compute_step_fix_success in Hcomp; repnd; subst.
        csunf; simpl; eexists; dands; eauto.

      - SSSSCase "NCbv".
        apply compute_step_cbv_success in Hcomp; exrepnd; subst.
        csunf; simpl; eexists; dands; eauto.

      - SSSSCase "NTryCatch".
        apply compute_step_try_success in Hcomp; exrepnd; subst.
        csunf; simpl; eexists; dands; eauto.

      - SSSSCase "NCanTest".
        apply compute_step_seq_can_test_success in Hcomp; exrepnd; subst.
        csunf; simpl; eexists; dands; eauto.
    }

    dopid arg1o as [arg1c | arg1nc | arg1exc | arg1abs] SSSSCase;
      try (complete (exists t2; auto)).

    + SSSSCase "Can". GC.
      dopid_noncan nc1 SSSSSCase; try (complete (exists t2; auto)).

      * SSSSSCase "NEApply".

        csunf Hcomp; allsimpl.
        apply compute_step_eapply_success in Hcomp; exrepnd; subst.
        repndors; exrepnd; subst; allsimpl.

        { apply compute_step_eapply2_success in Hcomp1; repnd; subst.
          repndors; exrepnd; subst; ginv.
          { allunfold @mk_lam; ginv; fold_terms; unfold mk_eapply.
            rw @compute_step_eapply_lam_iscan; auto.
            eexists; dands; eauto. }
          { allunfold @mk_nseq; ginv; fold_terms.
            csunf; simpl; dcwf h; simpl; boolvar; try lia.
            rw Znat.Nat2Z.id.
            eexists; dands; eauto. }
        }

        { unfold eapply_wf_def in Hcomp2; repndors; exrepnd; ginv.
          { allunfold @mk_nseq; ginv; allsimpl; fold_terms.
            rw @compute_step_eapply_iscan_isexc; simpl; eauto 3 with slow. }
          { allunfold @mk_lam; ginv.
            fold_terms; unfold mk_eapply.
            rw @compute_step_eapply_iscan_isexc; simpl; eauto 3 with slow.  }
        }

        { pose proof (IHind arg2 arg2 []) as h; clear IHind.
          repeat (autodimp h hyp); eauto 3 with slow.
          pose proof (h x) as ih; clear h.
          repeat (autodimp ih hyp); exrepnd.
          fold_terms; unfold mk_eapply.
          rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
          rw ih1; eexists; dands; eauto.
          prove_alpha_eq2. }

      * SSSSSCase "NCompOp".

        (* the next 2 cases are different because they have 2 prinargs
           i.e. they make recursive calls if the second arg is non-can
           *)

        destruct lbt1 as [| arg2]; try (complete (csunf Hcomp; allsimpl; dcwf h)).
        destruct arg2 as [lv2 nt2].
        destruct lv2; destruct nt2 as [?|?|arg2o arg2bts]; try (complete (csunf Hcomp; allsimpl; dcwf h)).

        dopid arg2o as [arg2c| arg2nc | arg2exc | arg2abs] SSSSSSCase;
          try (complete (simpl in Hcomp; exists t2; auto)).

        { SSSSSSCase "NCan".
          csunf Hcomp; allsimpl.
          dcwf h.
          unfold on_success in Hcomp.
          remember (compute_step lib1 ((oterm (NCan arg2nc) arg2bts))) as rec.
          destruct rec as [csuccrec | cfail]; inverts Hcomp as Hcomp.
          symmetry in Heqrec.
          eapply IHind with (lv:=[]) in Heqrec; eauto 3 with slow; tcsp;[].
          exrepnd; subst.
          exists (oterm (NCan (NCompOp c))
                        (bterm [] (oterm (Can arg1c) arg1bts)
                               :: bterm [] t2'
                               :: lbt1)).
          csunf; simpl.
          dcwf h;[].
          rewrite Heqrec1. split; [refl|].
          prove_alpha_eq2. }

        { SSSSSSCase "Abs".
          csunf Hcomp; allsimpl; csunf Hcomp; allsimpl.
          dcwf h.
          unfold on_success in Hcomp.
          remember (compute_step_lib lib1 arg2abs arg2bts) as csl.
          destruct csl; inversion Hcomp; subst; GC.
          symmetry in Heqcsl.

          pose proof (compute_step_lib_success lib1 arg2abs arg2bts n Heqcsl) as h.
          exrepnd; subst.
          duplicate h0 as fe1.
          eapply found_entry_alpha_eq_lib in h0; eauto; exrepnd.
          csunf; simpl; unfold on_success.
          csunf; simpl.
          dcwf h;[].
          exists (oterm (NCan (NCompOp c))
                        (bterm [] (oterm (Can arg1c) arg1bts)
                               :: bterm [] (mk_instance vars2 arg2bts rhs2)
                               :: lbt1)).
          duplicate h1 as fe2.
          apply found_entry_implies_compute_step_lib_success in h1; rw h1; dands; auto.
          prove_alpha_eq2.
          destruct XXn; auto.
          apply alphaeqbt_nilv2.

          apply found_entry_implies_matching_entry in fe1.
          apply found_entry_implies_matching_entry in fe2.
          unfold matching_entry in fe1; repnd.
          unfold matching_entry in fe2; repnd.

          allunfold @correct_abs; repnd.

          apply (alpha_eq_mk_abs_subst_if_bterm vs); auto. }

      * SSSSSCase "NArithOp".

        destruct lbt1 as [| arg2]; try (complete (csunf Hcomp; allsimpl; dcwf h)).
        destruct arg2 as [lv2 nt2].
        destruct lv2; destruct nt2 as [?|?| arg2o arg2bts]; try (complete (csunf Hcomp; allsimpl; dcwf h)).

        dopid arg2o as [arg2c| arg2nc | arg2exc | arg2abs] SSSSSSCase;
          try (complete (simpl in Hcomp; exists t2; auto)).

        { SSSSSSCase "NCan".
          csunf Hcomp; allsimpl.
          dcwf h.
          unfold on_success in Hcomp.
          remember (compute_step lib1 ((oterm (NCan arg2nc) arg2bts))) as rec.
          destruct rec as [csuccrec | cfail]; inverts Hcomp as Hcomp.
          symmetry in Heqrec.
          eapply IHind with (lv:=[]) in Heqrec; eauto 3 with slow; tcsp; [].
          exrepnd; subst.
          exists (oterm (NCan (NArithOp a))
                        (bterm [] (oterm (Can arg1c) arg1bts)
                               :: bterm [] t2'
                               :: lbt1)).
          csunf; simpl.
          dcwf h.
          rewrite Heqrec1. split; [refl|].
          prove_alpha_eq2. }

        { SSSSSSCase "Abs".
          csunf Hcomp; allsimpl.
          dcwf h;[].
          unfold on_success in Hcomp.
          csunf Hcomp; allsimpl.
          remember (compute_step_lib lib1 arg2abs arg2bts) as csl.
          destruct csl; inversion Hcomp; subst; GC.
          symmetry in Heqcsl.

          pose proof (compute_step_lib_success lib1 arg2abs arg2bts n Heqcsl) as h.
          exrepnd; subst.
          duplicate h0 as fe1.
          eapply found_entry_alpha_eq_lib in h0; eauto; exrepnd.
          csunf; simpl; unfold on_success.
          csunf; simpl.
          dcwf h;[].
          exists (oterm (NCan (NArithOp a))
                        (bterm [] (oterm (Can arg1c) arg1bts)
                               :: bterm [] (mk_instance vars2 arg2bts rhs2)
                               :: lbt1)).
          duplicate h1 as fe2.
          apply found_entry_implies_compute_step_lib_success in h1; rw h1; dands; auto.
          prove_alpha_eq2.
          destruct XXn; auto.
          apply alphaeqbt_nilv2.

          apply found_entry_implies_matching_entry in fe1.
          apply found_entry_implies_matching_entry in fe2.
          unfold matching_entry in fe1; repnd.
          unfold matching_entry in fe2; repnd.

          allunfold @correct_abs; repnd.

          apply (alpha_eq_mk_abs_subst_if_bterm vs); auto. }

    + SSSSCase "NCan". GC.
      csunf Hcomp; allsimpl.
      remember (compute_step lib1 (oterm (NCan arg1nc) arg1bts)) as crt2s.
      symmetry in Heqcrt2s.
      destruct crt2s as [csucct2s | cfail];
        try (complete (inversion Hcomp)).
      inverts Hcomp.

      eapply IHind with (lv:=[]) in Heqcrt2s; eauto 3 with slow; try(simpl; left; auto); exrepnd.
      exists ((oterm (NCan nc1) (bterm [] t2' :: lbt1))).
      rename Heqcrt2s1 into Hcomp.
      rename Heqcrt2s0 into H1alcarg.
      csunf; simpl.
      rw Hcomp. split; [refl|].
      constructor; auto.
      simpl. introv Hlt.
      destruct n; tcsp; unfold selectbt; simpl.
      apply alphaeqbt_nilv2; trivial.

    + SSSSCase "Abs".

      clear IHind.
      csunf Hcomp; simpl in Hcomp.
      csunf Hcomp; allsimpl.
      unfold on_success in Hcomp.
      remember (compute_step_lib lib1 arg1abs arg1bts) as c.
      destruct c; inversion Hcomp; subst; GC; symmetry in Heqc.
      pose proof (compute_step_lib_success lib1 arg1abs arg1bts n Heqc) as h.
      exrepnd; subst.

      csunf; simpl; unfold on_success.
      csunf; simpl.
      duplicate h0 as fe1.
      eapply found_entry_alpha_eq_lib in h0; eauto; exrepnd.
      duplicate h1 as fe2.
      apply found_entry_implies_compute_step_lib_success in h1; rw h1; dands; auto.
      eexists; dands; eauto.
      prove_alpha_eq2.
      destruct XXn; auto.
      apply alphaeqbt_nilv2.

      apply found_entry_implies_matching_entry in fe1.
      apply found_entry_implies_matching_entry in fe2.
      unfold matching_entry in fe1; repnd.
      unfold matching_entry in fe2; repnd.

      allunfold @correct_abs; repnd.

      apply (alpha_eq_mk_abs_subst_if_bterm vs); auto.
    }

    { (* fresh case *)
      csunf Hcomp; allsimpl.
      apply compute_step_fresh_success in Hcomp; repnd; subst; allsimpl.
      repndors; exrepnd; subst.

      - csunf; simpl; boolvar.
        eexists; dands; eauto.

      - rw @compute_step_fresh_if_isvalue_like2; auto.
        eexists; dands; eauto.

      - rw @compute_step_fresh_if_isnoncan_like; auto.
        pose proof (IHind
                      arg1nt
                      (subst arg1nt arg1v1 (mk_utoken (get_fresh_atom arg1nt)))
                      [arg1v1])
          as ih; clear IHind.
        repeat (autodimp ih hyp).
        { rw @simple_osize_subst; eauto 3 with slow. }
        pose proof (ih x) as h; clear ih; repeat (autodimp h hyp).
        exrepnd.
        rw h1; simpl.
        eexists; dands; eauto.
        apply implies_alpha_eq_mk_fresh.
        apply alpha_eq_subst_utokens; eauto with slow.
    }

  - SCase "Exc".
    csunf Hcomp; allsimpl; ginv.
    exists (oterm Exc lbt1); simpl; auto.

  - SCase "Abs".

    clear IHind.
    csunf Hcomp; simpl in Hcomp.
    pose proof (compute_step_lib_success lib1 abs1 lbt1 t2 Hcomp) as h.
    exrepnd; subst.

    simpl.
    duplicate h0 as fe1.
    eapply found_entry_alpha_eq_lib in h0; eauto; exrepnd.
    duplicate h1 as fe2.
    csunf; simpl.
    apply found_entry_implies_compute_step_lib_success in h1; rw h1; dands; auto.
    eexists; dands; eauto.

    apply found_entry_implies_matching_entry in fe1.
    apply found_entry_implies_matching_entry in fe2.
    unfold matching_entry in fe1; repnd.
    unfold matching_entry in fe2; repnd.

    allunfold @correct_abs; repnd.

    apply (alpha_eq_mk_abs_subst_if_bterm vs); auto.
Qed.

Lemma compute_1step_alpha_lib {p} :
  forall lib1 lib2 (t1 t2 : @NTerm p),
    alpha_eq_lib lib1 lib2
    -> computes_in_1step lib1 t1 t2
    -> {t2' : @NTerm p & computes_in_1step lib2 t1 t2' # alpha_eq t2 t2'}.
Proof.
  introv Hal Hc.
  invertsn Hc;
    eapply compute_step_alpha_lib in Hc; eauto; exrepnd;
    exists t2'; dands; auto;
    constructor; auto.
Qed.

Lemma computes_in_1step_alpha_lib {o} :
  forall (lib1 lib2 : @library o) t1 t2,
    computes_in_1step_alpha lib1 t1 t2
    -> alpha_eq_lib lib1 lib2
    -> computes_in_1step_alpha lib2 t1 t2.
Proof.
  introv comp aeq.
  allunfold @computes_in_1step_alpha; exrepnd.
  eapply compute_1step_alpha_lib in comp1; eauto; exrepnd.
  exists t2'; dands; eauto with slow.
Qed.

Lemma alpha_eq_entry_sym {o} :
  forall (entry1 entry2 : @library_entry o),
    alpha_eq_entry entry1 entry2 -> alpha_eq_entry entry2 entry1.
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? ? ? ? len1 len2 disj norep m a l1 l2]; subst; clear aeq.
  apply (aeq_lib_entry vs); eauto with slow.
  - allrw disjoint_app_r; sp.
  - apply matching_sovars_sym; auto.
Qed.
Hint Resolve alpha_eq_entry_sym : slow.

Lemma alpha_eq_lib_sym {o} :
  forall (lib1 lib2 : @library o),
    alpha_eq_lib lib1 lib2 -> alpha_eq_lib lib2 lib1.
Proof.
  induction lib1; introv aeq; inversion aeq; subst; auto.
  constructor; eauto with slow.
Qed.
Hint Resolve alpha_eq_lib_sym : slow.


Definition change_bvars_sobvars (vars : list sovar_sig) (vs : list NVar) : list sovar_sig :=
  map (fun x => match x with
                  | ((v1,n),v2) => (v2,n)
                end)
      (combine vars vs).

Definition change_bvars_abs {o} (disj : list NVar) (vars : list sovar_sig) (rhs : @SOTerm o) :=
  let vs := fresh_distinct_vars (length vars) (disj ++ sovars2vars vars ++ all_fo_vars rhs) in
  let vars' := change_bvars_sobvars vars vs in
  let rhs' := soswap (mk_soswapping vars vs) rhs in
  (vars', fo_change_bvars_alpha disj [] rhs').

Lemma rename_so_vars_mk_soren_spec1 :
  forall vs1 vs2 v n,
    length vs1 = length vs2 ->
    {v' : NVar & rename_sovar (mk_soren vs1 vs2) (v, n) = (v',n)
               # ((LIn (v,n) vs1
                   # LIn v' vs2
                   # LIn ((v,n),v') (mk_soren vs1 vs2))
                  [+]
                  (!LIn (v,n) vs1
                   # v = v'))}.
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  - exists v; simpl; sp; right; sp.
  - destruct a.
    rw rename_sovar_cons; boolvar; cpx.
    + exists n; sp.
    + pose proof (IHvs1 vs2 v n0 len) as h; exrepnd.
      exists v'; dands; auto.
      dorn h0; repnd; subst.
      * left; dands; tcsp.
      * right; rw not_over_or; sp.
Qed.

Lemma wf_soterm_soswap {o} :
  forall (t : @SOTerm o) sw,
    wf_soterm t <=> wf_soterm (soswap sw t).
Proof.
  soterm_ind t as [v ts ind | | op bs ind] Case;
  introv; allsimpl; tcsp.

  - Case "sovar".
    allrw @wf_sovar; split; intro k; introv i.
    + allrw in_map_iff; exrepnd; subst.
      apply ind; auto.
    + pose proof (k (soswap sw t)) as h.
      autodimp h hyp.
      { rw in_map_iff; eexists; eauto. }
      apply ind in h; auto.

  - Case "soterm".
    allrw @wf_soterm_iff; allrw map_map; unfold compose.
    split; intro k; repnd; dands; auto.

    + rw <- k0.
      apply eq_maps; introv i.
      destruct x; simpl.
      rw length_soswapbvars; auto.

    + introv i; allrw in_map_iff; exrepnd; subst.
      destruct a; allsimpl; ginv.
      applydup k in i1.
      eapply ind in i1; apply i1; auto.

    + rw <- k0.
      apply eq_maps; introv i.
      destruct x; simpl.
      rw length_soswapbvars; auto.

    + introv i.
      pose proof (k (soswapbvars sw vs) (soswap sw t)) as h.
      autodimp h hyp.
      { rw in_map_iff; eexists; eauto. }
      eapply ind in i; apply i in h; auto.
Qed.

Lemma soswapvar_eta :
  forall sw v n,
    (sovar2var (soswapvar sw (v, n)), n)
    = soswapvar sw (v, n).
Proof.
  induction sw; introv; simpl; auto.
  destruct a.
  destruct p; simpl.
  unfold onesoswapvar; boolvar; cpx.
Qed.

Lemma sovar2var_soswapvars_eq :
  forall vs1 vs2 (v1 v2 : NVar),
    !LIn v1 vs2
    -> !LIn v2 vs2
    -> no_repeats vs2
    -> sovar2var (soswapvar (mk_soswapping vs1 vs2) (var2sovar v1))
       = sovar2var (soswapvar (mk_soswapping vs1 vs2) (var2sovar v2))
    -> v1 = v2.
Proof.
  induction vs1; destruct vs2; introv ni1 ni2 norep e;
  allsimpl; tcsp; GC.
  - destruct a; allsimpl; auto.
  - destruct a; allsimpl.
    allrw no_repeats_cons; repnd.
    allrw not_over_or; repnd.
    unfold onesoswapvar in e; boolvar; allunfold var2sovar; cpx;
    apply IHvs1 in e; auto; subst; sp.
Qed.

Lemma so_free_vars_soswap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    disjoint vs2 (sovars2vars vs1)
    -> disjoint vs2 (all_fo_vars t)
    -> no_repeats vs2
    -> so_free_vars (soswap (mk_soswapping vs1 vs2) t)
       = map (soswapvar (mk_soswapping vs1 vs2)) (so_free_vars t).
Proof.
  soterm_ind t as [v ts ind | |op bs ind] Case;
  introv disj1 disj2 norep; allsimpl; auto.

  - Case "sovar".
    allrw map_length.
    allrw map_flat_map.
    allrw flat_map_map; unfold compose.
    rw soswapvar_eta.
    f_equal.
    apply eq_flat_maps; auto.
    allrw disjoint_cons_r; repnd.
    introv i.
    disj_flat_map.
    apply ind; auto.

  - Case "soterm".
    rw flat_map_map; rw map_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [l t]; simpl.
    disj_flat_map; allsimpl.
    allrw disjoint_app_r; repnd.
    erewrite ind; eauto.
    pose proof (sovars2vars_so_free_vars_subvars_all_fo_vars t) as sv.
    pose proof (subvars_disjoint_r
                  (sovars2vars (so_free_vars t))
                  (all_fo_vars t)
                  vs2) as d.
    repeat (autodimp d hyp).
    remember (so_free_vars t) as fv.

    clear ind i op.
    clear dependent t.
    clear dependent bs.
    induction fv; simpl.
    + allrw remove_so_vars_nil_r; auto.
    + allsimpl; allrw disjoint_cons_r; repnd.
      allrw remove_so_vars_cons_r; simpl; rw IHfv; auto; clear IHfv.
      boolvar; allsimpl; tcsp; provefalse.
      * destruct a as [v m].
        rw <- soswapvar_eta in l0.
        allrw in_vars2sovars; repnd; subst; allsimpl.
        allrw in_soswapbvars; exrepnd.
        apply disjoint_sym in i1.
        applydup i1 in l1.
        apply sovar2var_soswapvars_eq in l0; auto; subst; sp.
      * destruct a as [v m].
        rw <- soswapvar_eta in n.
        allrw in_vars2sovars; repnd; subst; allsimpl.
        destruct n; dands; auto.
        rw in_soswapbvars.
        exists v; auto.
Qed.

Lemma rename_sovar_is_soswapvar :
  forall vs1 vs2 v,
    disjoint vs2 (sovars2vars vs1)
    -> no_repeats vs2
    -> !LIn (sovar2var v) vs2
    -> rename_sovar (mk_soren vs1 vs2) v
       = soswapvar (mk_soswapping vs1 vs2) v.
Proof.
  induction vs1; destruct vs2; introv disj norep ni; allsimpl; tcsp; GC.
  - destruct a; auto.
  - destruct a; simpl.
    rw rename_sovar_cons.
    allrw not_over_or; repnd.
    allrw disjoint_cons_l; allrw disjoint_cons_r; repnd.
    allrw no_repeats_cons; repnd.
    allsimpl; allrw not_over_or; repnd.
    unfold onesoswapvar.
    boolvar; subst; cpx.
    rw soswapvar_not_in; auto.
Qed.

Lemma get_utokens_soswap {o} :
  forall s (t : @SOTerm o),
    get_utokens_so (soswap s t) = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind | |op bs ind] Case; introv; allsimpl; auto.

  - Case "sovar".
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; auto.

  - Case "soterm".
    apply app_if; auto.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    eapply ind; eauto.
Qed.

Lemma select_combine_some_implies :
  forall {A B} n (l1 : list A) (l2 : list B) a b,
    select n (combine l1 l2) = Some (a,b)
    -> select n l1 = Some a /\ select n l2 = Some b.
Proof.
  induction n; introv h; simpl in *.

  - destruct l1; simpl in *; ginv.
    destruct l2; simpl in *; ginv; tcsp.

  - destruct l1; simpl in *; ginv.
    destruct l2; simpl in *; ginv.
    apply IHn in h; auto.
Qed.

Lemma matching_sign_change_bvars_sobvars :
  forall vars fv sign,
    length vars = length fv
    -> matching_sign vars sign
    -> matching_sign (change_bvars_sobvars vars fv) sign.
Proof.
  introv len m.
  unfold matching_sign in *.
  unfold change_bvars_sobvars.
  rewrite map_map; unfold compose.
  subst.
  apply eq_maps3.
  { rewrite length_combine_eq; auto. }
  introv i; repnd; simpl in *.

  apply in_combine_sel_iff in i; exrepnd.
  symmetry in i3.
  apply select_combine_some_implies in i3; repnd.
  rewrite i4 in i0; ginv.
Qed.

Lemma correct_change_bvars_entry {o} :
  forall (disj    : list NVar)
         (opabs   : opabs)
         (vars    : list sovar_sig)
         (rhs     : @SOTerm o)
         (correct : correct_abs opabs vars rhs),
    match change_bvars_abs disj vars rhs with
      | (vars', rhs') => correct_abs opabs vars' rhs'
    end.
Proof.
  introv correct.
  simpl.

  pose proof (fresh_distinct_vars_spec
                (length vars)
                (disj ++ sovars2vars vars ++ all_fo_vars rhs))
    as h; simpl in h; repnd.
  remember (fresh_distinct_vars
              (length vars)
              (disj ++ sovars2vars vars ++ all_fo_vars rhs))
    as fv; clear Heqfv.
  allrw disjoint_app_r; repnd.

  allunfold @correct_abs; repnd; dands; auto.

  - apply wf_soterm_fo_change_bvars_alpha; auto.
    apply wf_soterm_soswap; auto.

  - allunfold @socovered.
    rw @so_free_vars_fo_change_bvars_alpha; simpl.
    rw map_rename_sovar_nil.
    rw @so_free_vars_soswap; auto.
    unfold change_bvars_sobvars.
    allrw subsovars_prop; introv i.
    allrw in_map_iff; exrepnd; subst.
    applydup correct1 in i1 as j.
    destruct a as [v n].
    exists ((v,n),fst (soswapvar (mk_soswapping vars fv) (v,n))); simpl.

    pose proof (rename_so_vars_mk_soren_spec1 vars fv v n) as s.
    autodimp s hyp; exrepnd.
    rw rename_sovar_is_soswapvar in s1; allsimpl; auto.
    + rw s1; simpl; dands; auto.
      dorn s0; tcsp.
    + intro k.
      apply h3 in k; destruct k.
      rw in_sovars2vars.
      eexists; eauto.

  - apply matching_sign_change_bvars_sobvars; auto.

  - pose proof (fo_change_bvars_alpha_spec
                  disj (soswap (mk_soswapping vars fv) rhs)) as k.
    simpl in k; repnd.
    unfold no_utokens.
    apply get_utokens_so_soalphaeq in k; rw <- k.
    rw @get_utokens_soswap; auto.
Defined.

Definition change_bvars_alpha_entry {o} (disj : list NVar) (entry : @library_entry o) : @library_entry o.
Proof.
  destruct entry.
  pose proof (correct_change_bvars_entry disj opabs vars rhs correct) as h.
  destruct (change_bvars_abs disj vars rhs).
  exact (lib_abs opabs l s h).
Defined.

(*
Definition change_bvars_alpha_entry {o} (lv : list NVar) (entry : @library_entry o) :=
  match entry with
    | lib_abs opabs vars rhs correct =>
      match change_bvars_alphabt lv (bterm vars rhs) with
        | bterm vars' rhs' =>
          lib_abs
            opabs
            vars'
            rhs'
            (correct_change_bvars_entry lv opabs vars rhs correct)
      end
  end.
*)

Fixpoint change_bvars_alpha_lib {o} (lv : list NVar) (lib : @library o) :=
  match lib with
    | [] => []
    | entry :: lib =>
      change_bvars_alpha_entry lv entry
      :: change_bvars_alpha_lib lv lib
  end.

Lemma sovars2vars_change_bvars_sobvars :
  forall vs1 vs2,
    length vs1 = length vs2
    -> sovars2vars (change_bvars_sobvars vs1 vs2) = vs2.
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  destruct a; simpl.
  f_equal.
  fold (change_bvars_sobvars vs1 vs2); auto.
Qed.

Definition soren_range (ren : soren) : list NVar := map (fun v => snd v) ren.

Lemma soren_range_app :
  forall ren1 ren2,
    soren_range (ren1 ++ ren2) = soren_range ren1 ++ soren_range ren2.
Proof.
  introv; unfold soren_range; rw map_app; auto.
Qed.

Lemma soren_range_mk_soren :
  forall vs1 vs2,
    length vs1 = length vs2
    -> soren_range (mk_soren vs1 vs2) = vs2.
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  rw IHvs1; auto.
Qed.

Definition foren_range (ren : foren) : list NVar := map (fun v => snd v) ren.

Lemma foren_range_app :
  forall ren1 ren2,
    foren_range (ren1 ++ ren2) = foren_range ren1 ++ foren_range ren2.
Proof.
  introv; unfold foren_range; rw map_app; auto.
Qed.

Lemma foren_range_mk_foren :
  forall vs1 vs2,
    length vs1 = length vs2
    -> foren_range (mk_foren vs1 vs2) = vs2.
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  rw IHvs1; auto.
Qed.

Lemma disjoint_fo_bound_vars_so_change_bvars_alpha {o} :
  forall (t : @SOTerm o) ren d,
    disjoint d (soren_range ren)
    -> disjoint d (fo_bound_vars (so_change_bvars_alpha d ren t)).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv disj; eauto 2 with slow;
  allsimpl; allrw flat_map_map; unfold compose;
  rw disjoint_flat_map_r; introv i.

  - Case "sovar".
    apply ind; auto.

  - Case "soterm".
    destruct x as [l t]; simpl.
    pose proof (fresh_distinct_vars_spec
                  (length l)
                  (d ++ all_fo_vars t ++ soren_vars ren))
         as h; simpl in h; repnd.
    remember (fresh_distinct_vars
                (length l)
                (d ++ all_fo_vars t ++ soren_vars ren))
      as fv; clear Heqfv.
    allrw disjoint_app_r; repnd; dands; eauto with slow.

    eapply ind; eauto.
    rw soren_range_app.
    rw disjoint_app_r; dands; auto.
    rw soren_range_mk_soren; eauto with slow.
    rw length_vars2sovars; auto.
Qed.

Lemma disjoint_fo_bound_vars_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) ren d,
    disjoint d (foren_range ren)
    -> disjoint d (fo_bound_vars (fo_change_bvars_alpha d ren t)).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv disj;
  allsimpl; allrw flat_map_map; unfold compose;
  eauto 2 with slow.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw disjoint_flat_map_r; introv i.
    allrw in_map_iff; exrepnd; subst.
    apply ind; auto.

  - Case "soterm".
    rw disjoint_flat_map_r; introv i.
    destruct x as [l t]; simpl.
    pose proof (fresh_distinct_vars_spec
                  (length l)
                  (l ++ d ++ all_fo_vars t ++ foren_vars ren))
         as h; simpl in h; repnd.
    remember (fresh_distinct_vars
                (length l)
                (l ++ d ++ all_fo_vars t ++ foren_vars ren))
      as fv; clear Heqfv.
    allrw disjoint_app_r; repnd; dands; eauto with slow.

    eapply ind; eauto.
    rw foren_range_app.
    rw disjoint_app_r; dands; auto.
    rw foren_range_mk_foren; eauto with slow.
Qed.

Lemma length_change_bvars_sobvars :
  forall vs1 vs2,
    length vs1 = length vs2
    -> length (change_bvars_sobvars vs1 vs2) = length vs1.
Proof.
  introv len.
  unfold change_bvars_sobvars.
  rw map_length.
  rw @length_combine_eq; auto.
Qed.

Lemma matching_sovars_change_bvars_sobvars :
  forall vars vs,
    length vars = length vs
    -> matching_sovars vars (change_bvars_sobvars vars vs).
Proof.
  induction vars; destruct vs; introv len; allsimpl; cpx.
  destruct a.
  unfold change_bvars_sobvars; simpl.
  fold (change_bvars_sobvars vars vs).
  unfold matching_sovars; simpl.
  f_equal.
  apply IHvars; auto.
Qed.
Hint Resolve matching_sovars_change_bvars_sobvars : slow.

Tactic Notation "arw" constr(T) := repeat (onerw T; auto).

Lemma soswapvar_soswapvar :
  forall vs1 vs2 vs v,
    disjoint vs2 vs
    -> disjoint vs2 (sovars2vars vs1)
    -> disjoint vs (sovars2vars vs1)
    -> no_repeats vs2
    -> no_repeats vs
    -> !LIn (sovar2var v) vs
    -> !LIn (sovar2var v) vs2
    -> length vs1 = length vs2
    -> length vs1 = length vs
    -> soswapvar (mk_soswapping vs1 vs2) v
       = soswapvar (mk_soswapping (change_bvars_sobvars vs1 vs) vs2)
                   (soswapvar (mk_soswapping vs1 vs) v).
Proof.
  induction vs1; destruct vs2, vs;
  introv disj1 disj2 disj3 norep1 norep2 ni1 ni2 len1 len2;
  allsimpl; cpx.
  allrw disjoint_cons_r; allrw disjoint_cons_l; repnd; allsimpl.
  allrw no_repeats_cons; repnd.
  allrw not_over_or; repnd.
  destruct a as [x m]; allsimpl.
  destruct v as [y k]; allsimpl.
  try (fold (change_bvars_sobvars vs1 vs)).
  destruct (sovar_sig_dec (x,m) (y,k)) as [i|i]; cpx.
  - allrw onesoswapvar_eq.
    rw soswapvar_not_in; auto.
    rw soswapvar_not_in; auto.
    rw onesoswapvar_eq.
    rw soswapvar_not_in; auto.
    rw sovars2vars_change_bvars_sobvars; auto.
  - rw (onesoswapvar_not_in2 x n); auto; try (complete (sp; cpx)).
    rw (onesoswapvar_not_in2 x n0); auto; try (complete (sp; cpx)).
    rw onesoswapvar_not_in2; auto.
    + intro h.
      destruct (in_deq sovar_sig sovar_sig_dec (y,k) vs1) as [j|j].
      * pose proof (soswapvar_in vs1 vs (y,k)) as ivs;
        repeat (autodimp ivs hyp).
        rw h in ivs; allsimpl; sp.
      * rw soswapvar_not_in2 in h; auto; cpx.
    + intro h.
      destruct (in_deq sovar_sig sovar_sig_dec (y,k) vs1) as [j|j].
      * pose proof (soswapvar_in vs1 vs (y,k)) as ivs;
        repeat (autodimp ivs hyp).
        rw h in ivs; allsimpl; sp.
      * rw soswapvar_not_in2 in h; auto; cpx.
Qed.

Lemma soswapbvars_soswapbvars :
  forall vs1 vs2 vs l,
    disjoint vs2 vs
    -> disjoint vs2 (sovars2vars vs1)
    -> disjoint vs (sovars2vars vs1)
    -> disjoint vs2 l
    -> disjoint vs l
    -> no_repeats vs2
    -> no_repeats vs
    -> length vs1 = length vs2
    -> length vs1 = length vs
    -> soswapbvars (mk_soswapping (change_bvars_sobvars vs1 vs) vs2)
                   (soswapbvars (mk_soswapping vs1 vs) l)
       = soswapbvars (mk_soswapping vs1 vs2) l.
Proof.
  induction l;
  introv disj1 disj2 disj3 disj4 disj5 norep1 norep2 len1 len2;
  allsimpl; auto.
  destruct a as [v n].
  unfold var2sovar; simpl.
  rw soswapvar_eta.
  allrw disjoint_cons_r; repnd.
  rw <- soswapvar_soswapvar; allsimpl; auto.
  rw IHl; auto.
Qed.

Lemma so_alphaeq_soswap_so_change_bvars_alpha {o} :
  forall (t : @SOTerm o) vs1 vs2 vs,
    disjoint vs2 vs
    -> disjoint vs2 (sovars2vars vs1)
    -> disjoint vs (sovars2vars vs1)
    -> disjoint vs2 (all_fo_vars t)
    -> disjoint vs (all_fo_vars t)
    -> no_repeats vs2
    -> no_repeats vs
    -> length vs1 = length vs2
    -> length vs1 = length vs
    -> so_alphaeq (soswap (mk_soswapping vs1 vs2) t)
                  (soswap (mk_soswapping (change_bvars_sobvars vs1 vs) vs2)
                          (soswap (mk_soswapping vs1 vs) t)).
Proof.
  soterm_ind1s t as [v ts ind| |op bs ind] Case;
  introv disj1 disj2 disj3 disj4 disj5;
  introv norep1 norep2 len1 len2;
  allsimpl; eauto 2 with slow.

  - Case "sovar".
    allrw disjoint_cons_r; repnd.
    allrw map_length.
    allrw map_map; unfold compose.
    rw soswapvar_eta.
    rw <- soswapvar_soswapvar; auto.
    constructor; allrw map_length; auto.
    introv i.
    allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx.
    allrw in_combine_same; repnd; subst; allsimpl.
    disj_flat_map; allsimpl.
    apply ind; auto.

  - Case "soterm".
    constructor; allrw map_length; auto.
    introv i.
    allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2]; allsimpl.
    rw combine_map_l in i1.
    rw in_map_iff in i1; exrepnd; cpx; allsimpl.
    ginv.
    disj_flat_map; allsimpl; allrw disjoint_app_r; repnd.

    pose proof (fresh_vars
                  (length l1)
                  (l1
                     ++ vs2
                     ++ sovars2vars vs1
                     ++ all_fo_vars t1
                     ++ all_fo_vars (soswap (mk_soswapping vs1 vs) t1)
                     ++ sovars2vars (change_bvars_sobvars vs1 vs)
                     ++ soswapbvars (mk_soswapping vs1 vs) l1
                     ++ soswapbvars (mk_soswapping vs1 vs2) l1
                     ++ soswapbvars (mk_soswapping (change_bvars_sobvars vs1 vs) vs2) (soswapbvars (mk_soswapping vs1 vs) l1)
                     ++ all_fo_vars (soswap (mk_soswapping vs1 vs2) t1)
                     ++ all_fo_vars (soswap (mk_soswapping (change_bvars_sobvars vs1 vs) vs2)
                                            (soswap (mk_soswapping vs1 vs) t1))
               )) as fv; exrepnd.
    allrw disjoint_app_r; repnd.

    apply (soaeqbt _ lvn); allsimpl; allrw length_soswapbvars; auto; try lia.

    + allrw disjoint_app_r; dands; auto.

    + rw @so_swap_soswap; auto.
      rw soswapbvars_soswapbvars; auto.

      pose proof (ind
                    t1 t1
                    l1
                    i1
                    (le_refl (sosize t1))
                    vs1 vs2 vs
                 ) as h.
      repeat (autodimp h hyp).

      apply (so_alphaeq_add_so_swap2
               (soswapbvars (mk_soswapping vs1 vs2) l1)
               lvn) in h;
        auto; allsimpl; allrw length_soswapbvars; auto; try lia;
        try (complete (allrw disjoint_app_r; dands; auto)).

      eapply so_alphaeq_trans;[|exact h]; clear h.

      rw @so_swap_soswap; auto.
Qed.

Lemma change_bvars_alpha_entry_spec {p} :
  forall (lv : list NVar) (entry : @library_entry p),
    let entry' := change_bvars_alpha_entry lv entry in
    disjoint lv (sovars2vars (bound_vars_entry entry'))
    # alpha_eq_entry entry entry'.
Proof.
  introv; simpl.
  destruct entry; simpl.
  rw sovars2vars_app.
  rw disjoint_app_r.
  unfold so_bound_vars.
  rw sovars2vars_vars2sovars.
  pose proof (fresh_distinct_vars_spec
                (length vars)
                (lv ++ sovars2vars vars ++ all_fo_vars rhs))
    as h; simpl in h; repnd.
  dands; auto.

  - remember (fresh_distinct_vars
                (length vars)
                (lv ++ sovars2vars vars ++ all_fo_vars rhs)) as fv;
    clear Heqfv.
    allrw disjoint_app_r; repnd.
    rw sovars2vars_change_bvars_sobvars; eauto with slow.

  - remember (fresh_distinct_vars
                (length vars)
                (lv ++ sovars2vars vars ++ all_fo_vars rhs)) as fv;
    clear Heqfv.
    allrw disjoint_app_r; repnd.
    apply disjoint_fo_bound_vars_fo_change_bvars_alpha; simpl; auto.

  - pose proof (fresh_vars
                  (length vars)
                  (sovars2vars vars
                               ++ sovars2vars (change_bvars_sobvars vars
                                                                    (fresh_distinct_vars
                                                                       (length vars)
                                                                       (lv ++ sovars2vars vars ++ all_fo_vars rhs)))
                               ++ all_fo_vars rhs
                               ++ all_fo_vars (fo_change_bvars_alpha
                                                 lv []
                                                 (soswap
                                                    (mk_soswapping
                                                       vars
                                                       (fresh_distinct_vars
                                                          (length vars)
                                                          (lv ++ sovars2vars vars ++ all_fo_vars rhs)))
                                                    rhs))
                               ++ all_fo_vars (soswap (mk_soswapping vars (fresh_distinct_vars
                                                                             (length vars)
                                                                             (lv ++ sovars2vars vars ++ all_fo_vars rhs)))
                                                      rhs)
               )) as fv.
    exrepnd.
    allrw disjoint_app_r; repnd.
    apply (aeq_lib_entry lvn); eauto with slow.

    + remember (fresh_distinct_vars
                  (length vars)
                  (lv ++ sovars2vars vars ++ all_fo_vars rhs)) as fv;
      clear Heqfv.
      rw length_change_bvars_sobvars; auto.

    + allrw disjoint_app_r; dands; auto.

    + remember (fresh_distinct_vars
                  (length vars)
                  (lv ++ sovars2vars vars ++ all_fo_vars rhs)) as fv;
      clear Heqfv.
      arw sovars2vars_change_bvars_sobvars.

      pose proof (so_alphaeq_fo_change_bvars_alpha2
                    (soswap (mk_soswapping vars fv) rhs)
                    lv) as aeq.
      apply (so_alphaeq_soswap _ _ (change_bvars_sobvars vars fv) lvn) in aeq;
        auto; arw sovars2vars_change_bvars_sobvars; auto.
      eapply so_alphaeq_trans;[|exact aeq]; clear aeq.
      apply so_alphaeq_soswap_so_change_bvars_alpha; auto.
Qed.

Lemma change_bvars_alpha_lib_spec {p} :
  forall lv (lib : @library p),
    let lib' := change_bvars_alpha_lib lv lib in
    disjoint lv (sovars2vars (bound_vars_lib lib')) # alpha_eq_lib lib lib'.
Proof.
  induction lib; simpl; tcsp; allsimpl; repnd.
  pose proof (change_bvars_alpha_entry_spec lv a) as h; simpl in h; repnd.
  allrw sovars2vars_app.
  rw disjoint_app_r; dands; auto.
  constructor; auto.
Qed.

Lemma change_bvars_alpha_eq_lib {o} :
  forall lv lib,
    {lib' : @library o
     & disjoint lv (sovars2vars (bound_vars_lib lib'))
     # alpha_eq_lib lib lib'}.
Proof.
  introv.
  exists (change_bvars_alpha_lib lv lib).
  apply change_bvars_alpha_lib_spec.
Qed.
