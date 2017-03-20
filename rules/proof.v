(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export proof1.


(*
Lemma cequiv_open_unfold_lib {o} :
  forall lib,
    no_undefined_abs_in_lib lib
    -> forall (t : @NTerm o),
      wf_term t
      -> cequiv_open lib t (unfold_lib lib t).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv isp; allsimpl.

  - Case "vterm".
    rewrite unfold_lib_vterm; eauto 3 with slow.

  - Case "sterm".
    rewrite unfold_lib_sterm.
    apply implies_cequiv_open_sterm; eauto 3 with slow.
    rewrite <- unfold_lib_sterm.
    eauto 3 with slow.

  - Case "oterm".

Lemma unfold_library_oterm_comp {o} :
  forall lib op (bs : list (@BTerm o)),
    reduces_to_al
      lib
      (oterm op (unfold_library_bterms lib bs))
      (unfold_library lib (oterm op bs)).
Proof.
  induction lib; introv; simpl; autorewrite with slow; eauto 3 with slow.
  rewrite unfold_entry_op_eq.
  destruct (dec_op_abs op) as [d|d]; exrepnd; subst; allsimpl.

  - unfold unfold_abs_entry.
    destruct a; allsimpl.
    boolvar.

    + assert (found_entry
                (lib_abs opabs vars rhs correct :: lib)
                abs
                (map (unfold_entry_bterm (lib_abs opabs vars rhs correct)) bs)
                opabs vars rhs correct) as fe.
      {
        unfold found_entry; simpl.
        boolvar; tcsp.
        apply not_matching_entry_iff in n; tcsp.
      }

      pose proof (compute_step_lib_success_change_bs
                    (lib_abs opabs vars rhs correct :: lib)
                    abs opabs
                    (map (unfold_entry_bterm (lib_abs opabs vars rhs correct)) bs)
                    (unfold_library_bterms
                       lib
                       (map (unfold_entry_bterm (lib_abs opabs vars rhs correct)) bs))
                    vars rhs correct) as h.
      repeat (autodimp h hyp).
      {
        unfold unfold_library_bterms.
        allrw map_map.
        unfold compose, num_bvars; apply eq_maps; introv i.
        destruct x as [l t]; simpl; auto.
      }

      eapply reduces_to_al_if_split2;[exact h|].
      clear h.

      remember (map (unfold_entry_bterm (lib_abs opabs vars rhs correct)) bs) as bs'.

      unfold mk_instance.
      destruct rhs as [v ts|f|op bs1].

      *

Lemma sosub_sovar_alpha_eq {o} :
  forall var (ts : list (@SOTerm o)) sub,
    alpha_eq
      (sosub sub (sovar var ts))
      (match sosub_find sub (var, length ts) with
       | Some (sosk vs u) => lsubst u (combine vs (map (sosub sub) ts))
       | None => apply_list (mk_var var) (map (sosub sub) ts)
       end).
Proof.
  introv.
  pose proof (unfold_sosub sub (sovar var ts)) as h; exrepnd.
  inversion h2 as [? ? ? len imp| |]; subst; clear h2.
  rewrite h1; simpl.
  allsimpl.
  remember (sosub_find sub' (var, length ts2)) as sf; symmetry in Heqsf; destruct sf.

  - destruct s.
    pose proof (sosub_find_some_if_alphaeq_sosub
                  sub' sub (var, length ts2) (sosk l n)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.
    rewrite <- len in q0.
    rewrite q0.
    destruct sk'.

    applydup @sosub_find_some in Heqsf; repnd.
    applydup @sosub_find_some in q0; repnd.

    apply alphaeq_sk_iff_alphaeq_bterm2 in q1; simpl in q1.
    allrw disjoint_cons_l; repnd.

    assert (disjoint (sub_free_vars (combine l (map (sosub_aux sub') ts2)))
                     (bound_vars n)) as disj.
    {
      rewrite sub_free_vars_combine; autorewrite with slow; auto.
      rewrite flat_map_map; unfold compose.
      apply disjoint_sym.
      eapply disjoint_bound_vars_prop4; try (exact Heqsf1); eauto 2 with slow.
    }
    rewrite sub_free_vars_combine in disj; autorewrite with slow; auto.
    rewrite flat_map_map in disj; unfold compose in disj.

    rewrite <- lsubst_lsubst_aux;
      [|rewrite range_combine;autorewrite with slow;auto;
        rewrite flat_map_map;unfold compose;eauto 3 with slow
      ].

    eapply lsubst_alpha_congr4; try (exact q1);
    try (rewrite dom_sub_combine);autorewrite with slow; auto.

    apply implies_alphaeq_sub_range_combine; autorewrite with slow; auto; try omega.
    introv i.
    rewrite <- map_combine in i.
    apply in_map_iff in i; exrepnd; ginv.

    SearchAbout (alphaeq (sosub _ _) (sosub _ _)).

Qed.

      * admit.

      * admit.

      (* by cases on rhs? *)

      (*
      apply reduces_to_if_step.
      csunf; simpl.
      rewrite h; auto.
       *)

    + pose proof (IHlib
                    (Abs abs)
                    (map (unfold_entry_bterm (lib_abs opabs vars rhs correct)) bs))
        as q; clear IHlib.

      admit.

      (* Prove something like reduces_to_preserves_agreeing_libraries but
         assuming that the abstractions are not in the extension to the library.
         This is going to be useful in all 3 cases.
       *)

  - pose proof (IHlib op (map (unfold_entry_bterm a) bs)) as q; clear IHlib.

    admit.
Qed.

    pose proof (unfold_library_oterm_comp lib op bs) as h.

    eapply cequiv_open_trans;
      [|apply reduces_to_al_implies_cequiv_open;
         [|
          |]
      ].

    Focus 4.

    Check unfold_library_oterm_comp.
    SearchAbout cequiv_open reduces_to.

Lemma unfold_library_oterm {o} :
  forall lib,
    no_undefined_abs_in_lib lib
    ->
    forall op (bs : list (@BTerm o)),
      unfold_library lib (oterm op bs)
      = match dec_op_abs op with
        | inl (existT abs _) =>
          match unfold_abs lib abs bs with
          | Some t => unfold_library lib t
          | None => oterm op (unfold_library_bterms lib bs)
          end
        | _ => oterm op (unfold_library_bterms lib bs)
        end.
Proof.
  induction lib; introv noundef; introv; simpl; auto;
  autorewrite with slow; auto;
  destruct (dec_op_abs op) as [d|d]; exrepnd; subst; allsimpl; auto; repnd;
  autodimp IHlib hyp.

  - destruct a; allsimpl.
    boolvar.

    +

    + apply not_matching_entry_iff in n; destruct n.
      eapply matching_entry_change_bs;try (exact m).
      unfold unfold_library_bterms.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      destruct x as [l t]; unfold num_bvars; simpl; auto.

    + apply not_matching_entry_iff in n; destruct n.
      eapply matching_entry_change_bs;try (exact m).
      unfold unfold_library_bterms.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      destruct x as [l t]; unfold num_bvars; simpl; auto.

    + rewrite IHlib; simpl.
      destruct (dec_op_abs (Abs abs)) as [e|e]; exrepnd; ginv; auto.
      destruct e; eexists; eauto.

  - rewrite unfold_entry_op_eq.
    destruct (dec_op_abs op) as [e|e]; try (complete (destruct d; auto)); GC.
    rewrite IHlib.
    destruct (dec_op_abs op) as [e|e]; try (complete (destruct d; auto)); GC.
    auto.
Qed.

Qed.
*)

(* THIS IS WHERE I'M AT *)

(*
Lemma exists_all_defined {o} :
  forall lib,
    no_undefined_abs_in_lib lib
    -> forall (t : @NTerm o),
      isprog t
      -> cequiv lib t (unfold_lib lib t).
Proof.
  induction lib; intro nodef; simpl.

  - introv isp; dands.

    unfold unfold_lib; simpl.
    apply cequiv_nil_abs2bot; auto.

  - introv isp.
    unfold unfold_lib; allsimpl; repnd.
    autodimp IHlib hyp.
    pose proof (IHlib (unfold_entry a t)) as h; clear IHlib.
    autodimp h hyp; eauto 3 with slow; repnd.

    unfold unfold_lib in h.

    assert (cequiv
              (a :: lib)
              (unfold_entry a t)
              (abs2bot (unfold_library lib (unfold_entry a t)))) as ceq;
      [|eapply cequiv_trans;[|exact ceq];apply cequiv_unfold_entry;auto].

    (* we prove that using add_entry_to_cequiv (see below) *)

Fixpoint all_abstractions_not_defined {o} lib (t : @NTerm o) : obool :=
  match t with
  | vterm _ => otrue
  | sterm f => obseq (fun n => all_abstractions_not_defined lib (f n))
  | oterm op bs =>
    oband
      (bool2obool (negb (found_opid_in_library_sign lib op)))
      (oball (map (all_abstractions_not_defined_b lib) bs))
  end
with all_abstractions_not_defined_b {o} lib (b : @BTerm o) : obool :=
       match b with
       | bterm vs t => all_abstractions_not_defined lib t
       end.

Lemma add_entry_to_approx {o} :
  forall entry lib (t1 t2 : @NTerm o),
    wf_term t1
    -> wf_term t2
    -> isotrue (all_abstractions_not_defined [entry] t1)
    -> isotrue (all_abstractions_not_defined [entry] t2)
    -> approx lib t1 t2
    -> approx (entry :: lib) t1 t2.
Proof.
  nterm_ind t1 as [v|f ind|op bs ind] Case;
  introv wf1 wf2 iso1 iso2 apr; allsimpl; GC.

  Focus 2.

  - Case "vterm".
    inversion apr; subst.
    constructor.

Lemma approx_open_vterm_implies {o} :
  forall lib v (t : @NTerm o),
    approx_open lib (vterm v) t -> t = vterm v.
Proof.
  introv ceq.
  apply olift_cequiv_approx in ceq; repnd.
  clear ceq0.

  SearchAbout approx_open vterm.
Qed.

Qed.

Focus 2.

XXXXXXXXXXX

Qed.
 *)


Lemma free_vars_unfold_library {o} :
  forall lib (t : @NTerm o),
    subset (free_vars (unfold_library lib t)) (free_vars t).
Proof.
  induction lib; simpl; introv; auto.
  eapply subset_trans;[apply IHlib|].
  apply free_vars_unfold_entry.
Qed.

Lemma isprog_unfold_library {o} :
  forall lib (t : @NTerm o),
    isprog t
    -> isprog (unfold_library lib t).
Proof.
  introv isp; allrw @isprog_eq.
  inversion isp as [cl wf].
  constructor; allrw @nt_wf_eq; eauto 3 with slow.
  pose proof (free_vars_unfold_library lib t) as h.
  rewrite cl in h.
  apply subset_nil_implies_nil; auto.
Qed.

Lemma isprog_unfold_lib {o} :
  forall lib (t : @NTerm o),
    isprog t
    -> isprog (unfold_lib lib t).
Proof.
  introv isp.
  apply implies_isprog_abs2bot.
  apply isprog_unfold_library; auto.
Qed.

Definition unfold_libc {o} lib (t : @CTerm o) :=
  match t with
  | exist _ a p => mk_ct (unfold_lib lib a) (isprog_unfold_lib lib a p)
  end.

Lemma isotrue_all_abs_are_defined_unfold_lib {o} :
  forall lib1 lib2 (t : @NTerm o),
    isotrue (all_abstractions_are_defined lib1 (unfold_lib lib2 t)).
Proof.
  introv.
  apply isotrue_all_abs_are_defined_abs2bot.
Qed.

Lemma isotrue_all_abs_are_defined_cterm_unfold_libc {o} :
  forall lib1 lib2 (t : @CTerm o),
    isotrue (all_abstractions_are_defined_cterm lib1 (unfold_libc lib2 t)).
Proof.
  introv.
  destruct_cterms.
  unfold all_abstractions_are_defined_cterm; simpl.
  apply isotrue_all_abs_are_defined_unfold_lib.
Qed.
Hint Resolve isotrue_all_abs_are_defined_cterm_unfold_libc : slow.

Lemma isotrue_all_abs_are_defined_cterm_approx {o} :
  forall lib (a b : @CTerm o),
    isotrue (all_abstractions_are_defined_cterm lib a)
    -> isotrue (all_abstractions_are_defined_cterm lib b)
    -> isotrue (all_abstractions_are_defined_cterm lib (mkc_approx a b)).
Proof.
  introv h1 h2.
  destruct_cterms.
  allunfold @all_abstractions_are_defined_cterm; allsimpl.
  autorewrite with slow.
  apply isotrue_oband; auto.
Qed.

Lemma isotrue_all_abs_are_defined_cterm_cequiv {o} :
  forall lib (a b : @CTerm o),
    isotrue (all_abstractions_are_defined_cterm lib a)
    -> isotrue (all_abstractions_are_defined_cterm lib b)
    -> isotrue (all_abstractions_are_defined_cterm lib (mkc_cequiv a b)).
Proof.
  introv h1 h2.
  destruct_cterms.
  allunfold @all_abstractions_are_defined_cterm; allsimpl.
  autorewrite with slow.
  apply isotrue_oband; auto.
Qed.

Lemma cequivc_unfold_lib {o} :
  forall lib,
    no_undefined_abs_in_lib lib
    -> forall (t : @CTerm o),
      cequivc lib t (unfold_libc lib t).
Proof.
  (* see above *)
Admitted.

Definition ex_all_defined {o} lib (t : @CTerm o) :=
  {u : CTerm
   , ccequivc lib t u
   /\ isotrue (all_abstractions_are_defined_cterm lib u) }.

Lemma restrict_to_lib_eq_in_nuprl {o} :
  forall lib (T T' : @CTerm o) eq,
    no_undefined_abs_in_lib lib
    -> nuprl lib T T' eq
    ->
    (
      ex_all_defined lib T
      /\ forall t t', eq t t' -> ex_all_defined lib t
    ).
Proof.
  introv noundef n.
  dands.
  - pose proof (cequivc_unfold_lib lib noundef T) as h.
    exists (unfold_libc lib T); dands; spcast; eauto 3 with slow.
  - introv e.
    pose proof (cequivc_unfold_lib lib noundef t) as h.
    exists (unfold_libc lib t); dands; spcast; eauto 3 with slow.

    (*
  unfold nuprl in n.
  remember (univ lib) as ts.
  close_cases (induction n using @close_ind') Case; subst; introv.

  - Case "CL_init".
    duniv i h.

    revert dependent eq.
    revert dependent T.
    revert dependent T'.
    induction i; introv u; allsimpl; tcsp.
    repndors; exrepnd; spcast; try (complete (apply IHi in u; tcsp)).

    dands.

    + exists (@mkc_uni o i); dands; simpl; auto.
      spcast; eauto 3 with slow.

    + introv e.
      apply u in e; exrepnd.

      remember (univi lib i) as ts.
      close_cases (induction e0 using @close_ind') SCase; subst; introv.

      * SCase "CL_init".
        match goal with
        | [ H : univi _ _ _ _ _ |- _ ] => apply IHi in H; sp
        end.

      * SCase "CL_int".
        allunfold @per_int; repnd; spcast.
        exists (@mkc_int o); simpl; dands; spcast; eauto 3 with slow.

      * SCase "CL_atom".
        allunfold @per_atom; repnd; spcast.
        exists (@mkc_atom o); simpl; dands; spcast; eauto 3 with slow.

      * SCase "CL_uatom".
        allunfold @per_uatom; repnd; spcast.
        exists (@mkc_uatom o); simpl; dands; spcast; eauto 3 with slow.

      * SCase "CL_base".
        allunfold @per_base; repnd; spcast.
        exists (@mkc_base o); simpl; dands; spcast; eauto 3 with slow.

      * SCase "CL_approx".
        allunfold @per_approx; exrepnd; spcast.

        pose proof (cequivc_unfold_lib lib noundef a) as ha.
        pose proof (cequivc_unfold_lib lib noundef b) as hb.

        exists (mkc_approx (unfold_libc lib a) (unfold_libc lib b)); simpl; dands; spcast; eauto 3 with slow.

        {
          eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; eauto|].
          apply cequivc_decomp_approx; auto.
        }

        {
          apply isotrue_all_abs_are_defined_cterm_approx; eauto 3 with slow.
        }

      * SCase "CL_cequiv".
        allunfold @per_cequiv; exrepnd; spcast.

        pose proof (cequivc_unfold_lib lib noundef a) as ha.
        pose proof (cequivc_unfold_lib lib noundef b) as hb.

        exists (mkc_cequiv (unfold_libc lib a) (unfold_libc lib b)); simpl; dands; spcast; eauto 3 with slow.

        {
          eapply cequivc_trans;[apply computes_to_valc_implies_cequivc; eauto|].
          apply cequivc_decomp_cequiv; auto.
        }

        {
          apply isotrue_all_abs_are_defined_cterm_cequiv; eauto 3 with slow.
        }

      *
*)
Qed.

Lemma tequality_cons_library_entry {o} :
  forall lib1 lib2 (t1 t2 : @CTerm o) eq,
    assert (wf_library lib1)
    -> assert (wf_library lib2)
    -> libraries_agree_on_intersection lib1 lib2
    -> no_repeats_lib lib2
    -> simple_no_undefined_abs_in_lib lib1
    -> simple_no_undefined_abs_in_lib lib2
    -> isotrue (all_abstractions_are_defined_cterm lib1 t1)
    -> isotrue (all_abstractions_are_defined_cterm lib1 t2)
    -> isotrue (all_abstractions_are_defined_cterm lib2 t1)
    -> isotrue (all_abstractions_are_defined_cterm lib2 t2)
    -> nuprl lib1 t1 t2 eq
    -> nuprl lib2 t1 t2 eq.
Proof.
  introv wflib1 wflib2 agree norep undef1 undef2;
  introv iso11 iso12 iso21 iso22 n.
  allunfold @nuprl.

  remember (univ lib1) as ts.
  close_cases (induction n using @close_ind') Case; subst.

  (*
  - Case "CL_init".
    duniv i h.

    induction i; allsimpl; tcsp.
    repndors; exrepnd; spcast;
    try (complete (autodimp IHi hyp)).

    apply CL_init.
    exists (S i); simpl.
    left; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).
*)

(*
Focus 6.
  - Case "CL_approx".
    unfold per_approx in per; exrepnd; spcast.
    eexists.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @approx_stable_iff; auto.
*)

  Focus 11.

  - Case "CL_func".
    clear per; spcast.
    apply CL_func.
    unfold per_func.
    exists eqa eqb; dands; auto.
    unfold type_family.
    exists A A' v v' B B'; dands; spcast; auto.

    { apply (computes_to_value_preserves_agreeing_libraries lib1 lib2); eauto 2 with slow. }

    { apply (computes_to_value_preserves_agreeing_libraries lib1 lib2); eauto 2 with slow. }

    { apply IHn; auto.
      admit.
      admit.
      admit.
      admit.

    }

    {
      introv.

      apply recb; auto.
    }

XXXXXXXXXXXXXXXXXXX

    rename eq0 into eqa0.

    assert (forall a a' : CTerm,
               eqa a a' ->
               exists eq0,
                 close (e :: lib)
                       (univ (e :: lib))
                       (B) [[v \\ a]]
                       (B') [[v' \\ a']]
                       eq0) as recbb.
    { introv h; apply recb; auto. }
    clear recb.

    apply choice_teq0 in recbb; exrepnd.
    rename f into eqb0.

    exists (fun t t' =>
              forall a a' (e : eqa0 a a'),
                (eqb0 a a' e) (mkc_apply t a) (mkc_apply t' a')).

  - Case "CL_init".
    duniv i h.

    induction i; allsimpl; tcsp.
    repndors; exrepnd; spcast.

    + exists (fun A A' => exists eqa, close (e :: lib) (univi (e :: lib) i) A A' eqa).
      apply CL_init.
      exists (S i); simpl.
      left; dands; auto; spcast;
      try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

    + autodimp IHi hyp.

  - Case "CL_int".
    exists (equality_of_int (e :: lib)).
    apply CL_int.
    allunfold @per_int; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_atom".
    unfold per_atom in per; repnd; spcast.
    eexists.
    apply CL_atom.
    unfold per_atom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_uatom".
    unfold per_uatom in per; repnd; spcast.
    eexists.
    apply CL_uatom.
    unfold per_uatom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_base".
    unfold per_base in per; repnd; spcast.
    eexists.
    apply CL_base.
    unfold per_base; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_approx".
    unfold per_approx in per; exrepnd; spcast.
    eexists.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @approx_stable_iff; auto.

  - Case "CL_cequiv".
    unfold per_cequiv in per; exrepnd; spcast.
    eexists.
    apply CL_cequiv.
    unfold per_cequiv.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @cequiv_stable_iff; auto.

  - Case "CL_eq".
    clear per.
    autodimp IHteq0 hyp; exrepnd.
    eexists.
    apply CL_eq.
    unfold per_eq.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)); eauto.
    allrw @cequiv_stable_iff; auto.
Qed.

Lemma tequality_cons_library_entry {o} :
  forall lib e (t1 t2 : @CTerm o),
    !in_lib (opabs_of_lib_entry e) lib
    -> tequality lib t1 t2
    -> tequality (e :: lib) t1 t2.
Proof.
  introv p teq.
  allunfold @tequality; exrepnd.
  allunfold @nuprl.

  remember (univ lib) as ts.
  close_cases (induction teq0 using @close_ind') Case; subst.

  Focus 11.

  - Case "CL_func".
    clear per; spcast.
    autodimp IHteq0 hyp; exrepnd.
    rename eq0 into eqa0.

    assert (forall a a' : CTerm,
               eqa a a' ->
               exists eq0,
                 close (e :: lib)
                       (univ (e :: lib))
                       (B) [[v \\ a]]
                       (B') [[v' \\ a']]
                       eq0) as recbb.
    { introv h; apply recb; auto. }
    clear recb.

    apply choice_teq0 in recbb; exrepnd.
    rename f into eqb0.

    exists (fun t t' =>
              forall a a' (e : eqa0 a a'),
                (eqb0 a a' e) (mkc_apply t a) (mkc_apply t' a')).

  - Case "CL_init".
    duniv i h.

    induction i; allsimpl; tcsp.
    repndors; exrepnd; spcast.

    + exists (fun A A' => exists eqa, close (e :: lib) (univi (e :: lib) i) A A' eqa).
      apply CL_init.
      exists (S i); simpl.
      left; dands; auto; spcast;
      try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

    + autodimp IHi hyp.

  - Case "CL_int".
    exists (equality_of_int (e :: lib)).
    apply CL_int.
    allunfold @per_int; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_atom".
    unfold per_atom in per; repnd; spcast.
    eexists.
    apply CL_atom.
    unfold per_atom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_uatom".
    unfold per_uatom in per; repnd; spcast.
    eexists.
    apply CL_uatom.
    unfold per_uatom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_base".
    unfold per_base in per; repnd; spcast.
    eexists.
    apply CL_base.
    unfold per_base; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_approx".
    unfold per_approx in per; exrepnd; spcast.
    eexists.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @approx_stable_iff; auto.

  - Case "CL_cequiv".
    unfold per_cequiv in per; exrepnd; spcast.
    eexists.
    apply CL_cequiv.
    unfold per_cequiv.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @cequiv_stable_iff; auto.

  - Case "CL_eq".
    clear per.
    autodimp IHteq0 hyp; exrepnd.
    eexists.
    apply CL_eq.
    unfold per_eq.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)); eauto.
    allrw @cequiv_stable_iff; auto.
Qed.

Lemma cover_vars_nil_iff_closed {o} :
  forall (t : @NTerm o), cover_vars t [] <=> closed t.
Proof.
  introv.
  rw @cover_vars_eq; simpl.
  unfold closed.
  rw subvars_eq; split; intro h; try (rewrite h); auto.
  remember (free_vars t) as l; clear Heql; destruct l; auto.
  apply subset_cons_nil in h; tcsp.
Qed.

Lemma cover_vars_nil2closed {o} :
  forall {t : @NTerm o}, cover_vars t [] -> closed t.
Proof.
  introv cov.
  apply cover_vars_nil_iff_closed; auto.
Qed.

Lemma wfClosed2isprogram {o} :
  forall {t : @NTerm o},
    wf_term t
    -> closed t
    -> isprogram t.
Proof.
  introv w c.
  constructor; eauto 3 with slow.
Qed.

Definition mk_cterm_wc {o}
           (t : @NTerm o)
           (w : wf_term t)
           (c : cover_vars t []) : CTerm :=
  mk_cterm t (wfClosed2isprogram w (cover_vars_nil2closed c)).

Lemma lsubstc_sub_nil {o} :
  forall (t : @NTerm o) w c,
    lsubstc t w [] c = mk_cterm_wc t w c.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_nil.
Qed.

Lemma sequent_true2_cons_library_entry {o} :
  forall lib e (c : @conclusion o),
    sequent_true2 lib (mk_baresequent [] c)
    -> sequent_true2 (e :: lib) (mk_baresequent [] c).
Proof.
  introv h.
  allunfold @sequent_true2; exrepnd.
  exists c0.
  allrw @sequent_true_eq_VR.
  allunfold @VR_sequent_true; introv.
  pose proof (h0 s1 s2) as q; clear h0; simpl in *.
  intros sim hf.
  dup sim as sim'.
  apply similarity_nil_implies in sim'; repnd; subst; allsimpl.
  pose proof (q (sim_nil lib) (hyps_functionality_nil lib)) as h; clear q; repnd.

  dands.

  - clear h.

    match goal with [ |- tequality _ (lsubstc _ _ _ ?c) _ ] => let c := fresh "c" in remember c; clear_eq1 c end.
    match goal with [ |- tequality _ _ (lsubstc _ _ _ ?c) ] => let c := fresh "c" in remember c; clear_eq1 c end.
    match goal with [ H : tequality _ (lsubstc _ _ _ ?c) _ |- _ ] => let c := fresh "c" in remember c; clear_eq1 c end.
    match goal with [ H : tequality _ _ (lsubstc _ _ _ ?c) |- _ ] => let c := fresh "c" in remember c; clear_eq1 c end.
    proof_irr.
    allrw @lsubstc_sub_nil.

Qed.

(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall ctxt (seq : @baresequent o) (wf : wf_bseq seq),
    Library ctxt
    -> proof ctxt seq
    -> sequent_true2 ctxt seq.
Proof.
  introv wf Lib p.
  induction p
    as [ (* proved sequent       *) seq p
       | (* isect_eq             *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* approx_refl          *) a hs
       | (* cequiv_approx        *) a b e1 e2 hs p1 ih1 p2 ih2
       | (* approx_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* bottom_diverges      *) x hs js
       | (* cut                  *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base        *) a b e F H p1 ih1 ps ihs
       | (* hypothesis           *) x A G J
       | (* cequiv_subst_concl   *) C x a b t e H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq     *) a b e H p ih
       | (* cequiv_computation   *) a b H p ih
       | (* function elimination *) A B C a e ea f x z H J wa cova nizH nizJ dzf p1 ih1 p2 ih2
       ];
    allsimpl;
    allrw NVin_iff.

  -

Lemma seq_in_library_is_true {o} :
  forall (ctxt : @ProofContext o) c,
    Library ctxt
    -> LIn c (PC_conclusions ctxt)
    -> sequent_true2 ctxt (mk_baresequent [] c).
Proof.
  introv Lib.
  induction Lib; simpl; introv i; tcsp.
  - autodimp IHLib hyp.

Qed.

  - apply (rule_isect_equality2_true3 lib a1 a2 b1 b2 e1 e2 x1 x2 y i hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

  - apply (rule_approx_refl_true3 lib hs a); simpl; tcsp.

  - apply (rule_cequiv_approx2_true3 lib hs a b e1 e2); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply ih2; auto.
    apply (rule_cequiv_approx2_wf2 a b e1 e2 hs); simpl; tcsp.

  - apply (rule_approx_eq2_true3 lib a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

  - apply (rule_cequiv_eq2_true3 lib a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

  - apply (rule_bottom_diverges_true3 lib x hs js); simpl; tcsp.

  - apply (rule_cut_true3 lib hs B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

      * apply ih2.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

  - apply (rule_equal_in_base2_true3 lib H a b e F); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    unfold rule_equal_in_base2_rest in xx; apply in_mapin in xx; exrepnd; subst.
    pose proof (ihs a0 i) as hh; clear ihs.
    repeat (autodimp hh hyp).
    pose proof (rule_equal_in_base2_wf2 H a b e F) as w.
    apply w; simpl; tcsp.
    right.
    apply in_mapin; eauto.

  - apply (rule_hypothesis_true3 lib); simpl; tcsp.

  - apply (rule_cequiv_subst_concl2_true3 lib H x C a b t e); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply ih1.
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

    + apply ih2.
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

  - apply (rule_approx_member_eq2_true3 lib a b e); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply ih.
    apply (rule_approx_member_eq2_wf2 a b e H); simpl; tcsp.

  - apply (rule_cequiv_computation_true3 lib); simpl; tcsp.

  - apply (rule_function_elimination_true3 lib A B C a e ea f x z); simpl; tcsp.

    introv ih; repndors; subst; tcsp.

    + apply ih1.
      pose proof (rule_function_elimination_wf2 A B C a e ea f x z H J) as h.
      unfold wf_rule2, wf_subgoals2 in h; simpl in h.
      repeat (autodimp h hyp).

    + apply ih2.
      pose proof (rule_function_elimination_wf2 A B C a e ea f x z H J) as h.
      unfold wf_rule2, wf_subgoals2 in h; simpl in h.
      repeat (autodimp h hyp).
Qed.

Fixpoint map_option
         {T U : Type}
         (f : T -> option U)
         (l : list T) : option (list U) :=
  match l with
  | [] => Some []
  | t :: ts =>
    match f t, map_option f ts with
    | Some u, Some us => Some (u :: us)
    | _, _ => None
    end
  end.

Fixpoint map_option_in
         {T U : Type}
         (l : list T)
  : forall (f : forall (t : T) (i : LIn t l), option U), option (list U) :=
  match l with
  | [] => fun f => Some []
  | t :: ts =>
    fun f =>
      match f t (@inl (t = t) (LIn t ts) eq_refl), map_option_in ts (fun x i => f x (inr i)) with
      | Some u, Some us => Some (u :: us)
      | _, _ => None
      end
  end.

Fixpoint map_option_in_fun
         {T U}
         (l : list T)
  : (forall t, LIn t l -> option (U t)) -> option (forall t, LIn t l -> U t) :=
  match l with
  | [] => fun f => Some (fun t (i : LIn t []) => match i with end)
  | t :: ts =>
    fun (f : forall x, LIn x (t :: ts) -> option (U x)) =>
      match f t (@inl (t = t) (LIn t ts) eq_refl),
            map_option_in_fun ts (fun x i => f x (inr i)) with
      | Some u, Some g => Some (fun x (i : LIn x (t :: ts)) =>
                                   match i with
                                   | inl e => transport e u
                                   | inr j => g x j
                                   end)
      | _, _ => None
      end
  end.

Lemma map_option_in_fun2_lem :
  forall {T : Type }
         (l : list T)
         (U : forall (t : T) (i : LIn t l), Type)
         (f : forall (t : T) (i : LIn t l), option (U t i)),
    option (forall t (i : LIn t l), U t i).
Proof.
  induction l; introv f; simpl in *.
  - left; introv; destruct i.
  - pose proof (f a (inl eq_refl)) as opt1.
    destruct opt1 as [u|];[|right].
    pose proof (IHl (fun x i => U x (inr i)) (fun x i => f x (inr i))) as opt2.
    destruct opt2 as [g|];[|right].
    left.
    introv.
    destruct i as [i|i].
    + rewrite <- i.
      exact u.
    + apply g.
Defined.

Fixpoint map_option_in_fun2
         {T : Type }
         (l : list T)
  : forall (U : forall (t : T) (i : LIn t l), Type),
    (forall (t : T) (i : LIn t l), option (U t i))
    -> option (forall t (i : LIn t l), U t i) :=
  match l with
  | [] => fun U f => Some (fun t (i : LIn t []) => match i with end)
  | t :: ts =>
    fun (U : forall (x : T) (i : LIn x (t :: ts)), Type)
        (f : forall x (i : LIn x (t :: ts)), option (U x i)) =>
      match f t (@inl (t = t) (LIn t ts) eq_refl),
            @map_option_in_fun2 T ts (fun x i => U x (inr i)) (fun x i => f x (inr i))
            return option (forall x (i : LIn x (t :: ts)), U x i)
      with
      | Some u, Some g => Some (fun x (i : LIn x (t :: ts)) =>
                                  match i as s return U x s with
                                  | inl e =>
                                    internal_eq_rew_dep
                                      T t
                                      (fun (x : T) (i : t = x) => U x injL(i))
                                      u x e
                                  | inr j => g x j
                                  end)
      | _, _ => None
      end
  end.

Fixpoint finish_pre_proof
         {o} {seq : @pre_baresequent o} {h : bool} {lib}
         (prf: pre_proof h lib seq) : option (pre_proof false lib seq) :=
  match prf with
  | pre_proof_hole s e => None
  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match finish_pre_proof pa, finish_pre_proof pb with
    | Some p1, Some p2 => Some (pre_proof_isect_eq _ _ a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
    | _, _ => None
    end
  | pre_proof_approx_refl a H => Some (pre_proof_approx_refl _ _ a H)
  | pre_proof_cequiv_approx a b H p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_cequiv_approx _ _ a b H p1 p2)
    | _, _ => None
    end
  | pre_proof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_approx_eq _ _ a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end
  | pre_proof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_cequiv_eq _ _ a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end
  | pre_proof_bottom_diverges x H J => Some (pre_proof_bottom_diverges _ _ x H J)
  | pre_proof_cut B C x H wB cBH nixH pu pt =>
    match finish_pre_proof pu, finish_pre_proof pt with
    | Some p1, Some p2 => Some (pre_proof_cut _ _ B C x H wB cBH nixH p1 p2)
    | _, _ => None
    end
  | pre_proof_equal_in_base a b H p1 pl =>
    let op := map_option_in_fun (free_vars a) (fun v i => finish_pre_proof (pl v i)) in
    match finish_pre_proof p1, op with
    | Some p1, Some g => Some (pre_proof_equal_in_base _ _ a b H p1 g)
    | _, _ => None
    end
  | pre_proof_hypothesis x A G J => Some (pre_proof_hypothesis _ _ x A G J)
  | pre_proof_cequiv_subst_concl C x a b H wa wb ca cb p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_cequiv_subst_concl _ _ C x a b H wa wb ca cb p1 p2)
    | _, _ => None
    end
  | pre_proof_approx_member_eq a b H p1 =>
    match finish_pre_proof p1 with
    | Some p1 => Some (pre_proof_approx_member_eq _ _ a b H p1)
    | _ => None
    end
  | pre_proof_cequiv_computation a b H r => Some (pre_proof_cequiv_computation _ _ a b H r)
  | pre_proof_function_elimination A B C a f x z H J wa cova nizH nizJ dzf p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_function_elimination _ _ A B C a f x z H J wa cova nizH nizJ dzf p1 p2)
    | _, _ => None
    end
  end.

Definition pre2conclusion {o} (c : @pre_conclusion o) (e : @NTerm o) :=
  match c with
  | pre_concl_ext T => concl_ext T e
  | pre_concl_typ T => concl_typ T
  end.

Definition pre2baresequent {o} (s : @pre_baresequent o) (e : @NTerm o) :=
  mk_baresequent
    (pre_hyps s)
    (pre2conclusion (pre_concl s) e).

Definition ExtractProof {o} (seq : @pre_baresequent o) lib :=
  {e : NTerm & proof lib (pre2baresequent seq e)}.

Definition mkExtractProof {o} {lib}
           (seq : @pre_baresequent o)
           (e : @NTerm o)
           (p : proof lib (pre2baresequent seq e))
  : ExtractProof seq lib :=
  existT _ e p.

(* converts a pre-proof without holes to a proof without holes by
 * generating the extract
 *)
Fixpoint pre_proof2iproof
         {o} {seq : @pre_baresequent o} {lib}
         (prf : pre_proof false lib seq)
  : ExtractProof seq lib  :=
  match prf with
  | pre_proof_hole s e => match e with end
  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match pre_proof2iproof pa, pre_proof2iproof pb with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
        mk_axiom
        (proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH p1 p2)
 (* I need to generalize the rule a bit to allow any extract in subgoals *)
    end
  | pre_proof_approx_refl a H =>
    mkExtractProof
      (pre_rule_approx_refl_concl a H)
      mk_axiom
      (proof_approx_refl _ a H)
  | pre_proof_cequiv_approx a b H p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_cequiv_approx_concl a b H)
        mk_axiom
        (proof_cequiv_approx _ a b e1 e2 H p1 p2)
    end
  | pre_proof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_approx_eq_concl a1 a2 b1 b2 i H)
        mk_axiom
        (proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2)
    end
  | pre_proof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H)
        mk_axiom
        (proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2)
    end
  | pre_proof_bottom_diverges x H J =>
    mkExtractProof
      (pre_rule_bottom_diverges_concl x H J)
      mk_bottom
      (proof_bottom_diverges _ x H J)
  | pre_proof_cut B C x H wB cBH nixH pu pt =>
    match pre_proof2iproof pu, pre_proof2iproof pt with
    | existT u p1, existT t p2 =>
      mkExtractProof
        (pre_rule_cut_concl H C)
        (subst t x u)
        (proof_cut _ B C t u x H wB cBH nixH p1 p2)
    end
  | pre_proof_equal_in_base a b H p1 pl =>
    let F := fun v (i : LIn v (free_vars a)) => pre_proof2iproof (pl v i) in
    let E := fun v i => projT1 (F v i) in
    let P := fun v i => projT2 (F v i) in
    match pre_proof2iproof p1 with
    | existT e p1 =>
      mkExtractProof
        (pre_rule_equal_in_base_concl a b H)
        mk_axiom
        (proof_equal_in_base _ a b e E H p1 P)
    end
  | pre_proof_hypothesis x A G J =>
    mkExtractProof
      (pre_rule_hypothesis_concl G J A x)
      (mk_var x)
      (proof_hypothesis _ x A G J)
  | pre_proof_cequiv_subst_concl C x a b H wa wb ca cb p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT t p1, existT e p2 =>
      mkExtractProof
        (pre_rule_cequiv_subst_hyp1 H x C a)
        t
        (proof_cequiv_subst_concl _ C x a b t e H wa wb ca cb p1 p2)
    end
  | pre_proof_approx_member_eq a b H p1 =>
    match pre_proof2iproof p1 with
    | existT e1 p1 =>
      mkExtractProof
        (pre_rule_approx_member_eq_concl a b H)
        mk_axiom
        (proof_approx_member_eq _ a b e1 H p1)
    end
  | pre_proof_cequiv_computation a b H r =>
    mkExtractProof
      (pre_rule_cequiv_concl a b H)
      mk_axiom
      (proof_cequiv_computation _ a b H r)
  | pre_proof_function_elimination A B C a f x z H J wa cova nizH nizJ dzf p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT ea p1, existT e p2 =>
      mkExtractProof
        (pre_rule_function_elimination_concl A B C f x H J)
        (subst e z mk_axiom)
        (proof_function_elimination _ A B C a e ea f x z H J wa cova nizH nizJ dzf p1 p2)
    end
  end.

Lemma test {o} :
  @sequent_true2 o emlib (mk_baresequent [] (mk_conclax ((mk_member mk_axiom mk_unit)))).
Proof.
  apply valid_proof;
  [ exact (eq_refl, (eq_refl, eq_refl))
  | exact (proof_approx_member_eq emlib (mk_axiom) (mk_axiom) (mk_axiom) (nil) (proof_approx_refl emlib (mk_axiom) (nil)))
          (* This last bit was generated by JonPRL; I've got to generate the whole thing now *)
  ].
Qed.


(*
Inductive test : nat -> Type :=
| Foo : test 1
| Bar : test 0.

(* works *)
Definition xxx {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | Bar => Bar
  end.

(* works *)
Definition yyy {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | x => x
  end.

(* works *)
Definition www {n : nat} (t : test n) : option (test n) :=
  match t with
  | Foo => Some Foo
  | Bar => None
  end.

(* doesn't work *)
Definition zzz {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | Bar => t
  end.
*)

Definition proof_update_fun {o} lib (s seq : @baresequent o) :=
  proof lib s -> proof lib seq.

Definition proof_update {o} lib (seq : @baresequent o) :=
  {s : @baresequent o & proof_update_fun lib s seq}.

Definition ProofUpdate {o} lib (seq : @baresequent o) :=
  option (proof_update lib seq).

Definition retProofUpd
           {o} {lib} {seq : @baresequent o}
           (s : @baresequent o)
           (f : proof lib s -> proof lib seq)
  : ProofUpdate lib seq :=
  Some (existT _ s f).

Definition idProofUpd
           {o} {lib}
           (seq : @baresequent o)
  : ProofUpdate lib seq :=
  retProofUpd seq (fun p => p).

Definition noProofUpd {o} {lib} {seq : @baresequent o}
  : ProofUpdate lib seq :=
  None.

Definition bindProofUpd
           {o} {lib} {seq1 seq2 : @baresequent o}
           (pu  : ProofUpdate lib seq1)
           (puf : proof lib seq1 -> proof lib seq2)
  : ProofUpdate lib seq2 :=
  match pu with
  | Some (existT s f) => retProofUpd s (fun p => puf (f p))
  | None => None
  end.

Definition address := list nat.

Fixpoint get_sequent_fun_at_address {o}
         {lib}
         {seq  : @baresequent o}
         (prf  : proof lib seq)
         (addr : address) : ProofUpdate lib seq :=
  match prf with
  | proof_isect_eq a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH pa pb =>
    match addr with
    | [] => idProofUpd (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pa addr)
        (fun x => proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH x pb)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pb addr)
        (fun x => proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH pa x)
    | _ => noProofUpd
    end
  | proof_approx_refl a H =>
    match addr with
    | [] => idProofUpd (rule_approx_refl_concl a H)
    | _ => noProofUpd
    end
  | proof_cequiv_approx a b e1 e2 H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_approx_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => proof_cequiv_approx _ a b e1 e2 H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => proof_cequiv_approx _ a b e1 e2 H p1 x)
    | _ => noProofUpd
    end
  | proof_approx_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_approx_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H p1 x)
    | _ => noProofUpd
    end
  | proof_cequiv_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H p1 x)
    | _ => noProofUpd
    end
  | proof_bottom_diverges x H J =>
    match addr with
    | [] => idProofUpd (rule_bottom_diverges_concl x H J)
    | _ => noProofUpd
    end
  | proof_cut B C t u x H wB cBH nixH pu pt =>
    match addr with
    | [] => idProofUpd (rule_cut_concl H C t x u)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pu addr)
        (fun z => proof_cut _ B C t u x H wB cBH nixH z pt)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pt addr)
        (fun z => proof_cut _ B C t u x H wB cBH nixH pu z)
    | _ => noProofUpd
    end
  | proof_equal_in_base a b e F H p1 pl =>
    match addr with
    | [] => idProofUpd (rule_equal_in_base_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => proof_equal_in_base _ a b e F H z pl)
    | _ => noProofUpd (* TODO *)
    end
  | proof_hypothesis x A G J =>
    match addr with
    | [] => idProofUpd (rule_hypothesis_concl G J A x)
    | _ => noProofUpd
    end
  | proof_cequiv_subst_concl C x a b t e H wa wb ca cb p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_subst_hyp1 H x C a t)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => proof_cequiv_subst_concl _ C x a b t e H wa wb ca cb z p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun z => proof_cequiv_subst_concl _ C x a b t e H wa wb ca cb p1 z)
    | _ => noProofUpd
    end
  | proof_approx_member_eq a b e H p1 =>
    match addr with
    | [] => idProofUpd (rule_approx_member_eq_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => proof_approx_member_eq _ a b e H z)
    | _ => noProofUpd
    end
  | proof_cequiv_computation a b H r =>
    match addr with
    | [] => idProofUpd (rule_cequiv_concl a b H)
    | _ => noProofUpd
    end
  | proof_function_elimination A B C a e ea f x z H J wa cova nizH nizJ dzf p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_function_elimination_concl A B C e f x z H J)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun p => proof_function_elimination _ A B C a e ea f x z H J wa cova nizH nizJ dzf p p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun p => proof_function_elimination _ A B C a e ea f x z H J wa cova nizH nizJ dzf p1 p)
    | _ => noProofUpd
    end
  end.

Fixpoint get_sequent_at_address {o}
           {seq  : @baresequent o}
           {lib}
           (prf  : proof lib seq)
           (addr : address) : option baresequent :=
  match get_sequent_fun_at_address prf addr with
  | Some (existT s _) => Some s
  | _ => None
  end.

Definition list1 {T} : forall a : T, LIn a [a].
Proof.
  tcsp.
Qed.


(* Looking at how we can define a Nuprl process *)

Inductive command {o} :=
(* add a definition at the head *)
| COM_add_def :
    forall (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : @SOTerm o)
           (correct : correct_abs opabs vars rhs),
      command
(* tries to complete a proof if it has no holes *)
| COM_finish_proof :
    ProofName -> command
(* focuses to a node in a proof *)
| COM_focus_proof :
    ProofName -> address -> command.

Definition proof_library {o} lib := list (@proof_library_entry o lib).

Record proof_update_seq {o} lib :=
  MkProofUpdateSeq
    {
      PUS_name  : ProofName;
      PUS_seq   : @baresequent o;
      PUS_focus : baresequent;
      PUS_upd   : proof_update_fun lib PUS_focus PUS_seq
    }.

Definition ProofUpdateSeq {o} lib :=
  option (@proof_update_seq o lib).

Record NuprlState {o} :=
  MkNuprlState
    {
      NuprlState_def_library   : @library o;
      NuprlState_proof_library : @proof_library o NuprlState_def_library;
      NuprlState_focus         : @ProofUpdateSeq o NuprlState_def_library
    }.

Fixpoint proof_consistent_with_new_definition
         {o} {seq : @baresequent o} {lib}
         (prf : proof lib seq)
         (e   : library_entry)
         (p   : !in_lib (opabs_of_lib_entry e) lib)
  : proof (e :: lib) seq :=
  match prf with
  | proof_isect_eq a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH pa pb =>
    let p1 := proof_consistent_with_new_definition pa e p in
    let p2 := proof_consistent_with_new_definition pb e p in
    proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH p1 p2
  | proof_approx_refl a H => proof_approx_refl _ a H
  | proof_cequiv_approx a b e1 e2 H p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_cequiv_approx _ a b e1 e2 H p1 p2
  | proof_approx_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2
  | proof_cequiv_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2
  | proof_bottom_diverges x H J => proof_bottom_diverges _ x H J
  | proof_cut B C t u x H wB cBH nixH pu pt =>
    let p1 := proof_consistent_with_new_definition pu e p in
    let p2 := proof_consistent_with_new_definition pt e p in
    proof_cut _ B C t u x H wB cBH nixH p1 p2
  | proof_equal_in_base a b ee F H p1 pl =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let g := fun v (i : LIn v (free_vars a)) => proof_consistent_with_new_definition (pl v i) e p in
    proof_equal_in_base _ a b ee F H p1 g
  | proof_hypothesis x A G J => proof_hypothesis _ x A G J
  | proof_cequiv_subst_concl C x a b t ee H wa wb ca cb p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_cequiv_subst_concl _ C x a b t ee H wa wb ca cb p1 p2
  | proof_approx_member_eq a b ee H p1 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    proof_approx_member_eq _ a b ee H p1
  | proof_cequiv_computation a b H r =>
    proof_cequiv_computation
      _ a b H
      (reduces_to_consistent_with_new_definition a b r e p)
  | proof_function_elimination A B C a ee ea f x z H J wa cova nizH nizJ dzf p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_function_elimination _ A B C a ee ea f x z H J wa cova nizH nizJ dzf p1 p2
  end.

Definition NuprlState_add_def_lib {o}
           (state   : @NuprlState o)
           (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : SOTerm)
           (correct : correct_abs opabs vars rhs) : NuprlState :=
  let lib := NuprlState_def_library state in
  match in_lib_dec opabs lib with
  | inl _ => state
  | inr p =>
    @MkNuprlState
      o
      (lib_abs opabs vars rhs correct :: lib)
      (NuprlState_proof_library state)
      (NuprlState_focus state)
  end.

Definition NuprlState_upd_proof_lib {o}
           (state : @NuprlState o)
           (lib   : @proof_library o) : NuprlState :=
  @MkNuprlState
    o
    (NuprlState_def_library state)
    lib
    (NuprlState_focus state).

Definition NuprlState_upd_focus {o}
           (state : @NuprlState o)
           (upd   : @ProofUpdateSeq o) : NuprlState :=
  @MkNuprlState
    o
    (NuprlState_def_library state)
    (NuprlState_proof_library state)
    upd.

Definition proof_library_entry_upd_proof {o} {lib}
           (e : @proof_library_entry o lib)
           (p : proof lib (proof_library_entry_seq lib e))
  : proof_library_entry lib :=
  MkProofLibEntry
    _
    _
    (proof_library_entry_name _ e)
    (proof_library_entry_seq _ e)
    h
    p.

Fixpoint finish_proof_in_library {o}
           (lib : @proof_library o)
           (name : ProofName) : proof_library :=
  match lib with
  | [] => []
  | p :: ps =>
    if String.string_dec (proof_library_entry_name p) name
    then if proof_library_entry_hole p (* no need to finish the proof if it is already finished *)
         then let p' := option_with_default
                          (option_map (fun p' => proof_library_entry_upd_proof p p')
                                      (finish_proof (proof_library_entry_proof p)))
                          p
              in p' :: ps
         else p :: ps
    else p :: finish_proof_in_library ps name
  end.

Fixpoint focus_proof_in_library {o}
           (lib : @proof_library o)
           (name : ProofName)
           (addr : address) : ProofUpdateSeq :=
  match lib with
  | [] => None
  | p :: ps =>
    if String.string_dec (proof_library_entry_name p) name
    then match get_sequent_fun_at_address (proof_library_entry_proof p) addr with
         | Some (existT s f) =>
           Some (MkProofUpdateSeq
                   o
                   name
                   (proof_library_entry_hole p)
                   (proof_library_entry_seq p)
                   s
                   f)
         | None => None
         end
    else focus_proof_in_library ps name addr
  end.

Definition update {o}
           (state : @NuprlState o)
           (com   : command) : NuprlState :=
  match com with
  | COM_add_def opabs vars rhs correct =>
    NuprlState_add_def_lib state opabs vars rhs correct
  | COM_finish_proof name =>
    let lib := NuprlState_proof_library state in
    NuprlState_upd_proof_lib state (finish_proof_in_library lib name)
  | COM_focus_proof name addr =>
    let lib := NuprlState_proof_library state in
    NuprlState_upd_focus state (focus_proof_in_library lib name addr)
  end.

CoInductive Loop {o} : Type :=
| proc : (@command o -> Loop) -> Loop.

CoFixpoint loop {o} (state : @NuprlState o) : Loop :=
  proc (fun c => loop (update state c)).
