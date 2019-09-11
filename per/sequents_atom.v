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


Require Export sequents_tacs.
Require Export atoms.
Require Export lsubst_hyps.
Require Export list. (* why? *)


Lemma fold_set_patom_string :
  forall p, set_patom p dset_string = set_dset_string p.
Proof. sp. Qed.

(* !! MOVE to atoms *)
Definition get_utokens_so_bs {p} (bts : list (@SOBTerm p)) : list (get_patom_set p) :=
  flat_map get_utokens_b_so bts.

(* !! MOVE to atoms *)
Definition get_utokens_so_ts {p} (ts : list (@SOTerm p)) : list (get_patom_set p) :=
  flat_map get_utokens_so ts.





Definition has_at_least_k_elements (k : nat) (D : Set) :=
  {l : list D & length l = k # no_repeats l}.

Lemma has_at_least_0_elements :
  forall D : Set, has_at_least_k_elements 0 D.
Proof.
  introv; exists ([] : list D); simpl; sp.
Qed.
Hint Immediate has_at_least_0_elements.




(* =============================================================== *)

Section ProofIrrelevantDSetMembership.

  Lemma deq_member {A} (deq : Deq A) :
    forall (x : A) l, LIn x l [+] !(LIn x l).
  Proof.
    induction l; simpl.
    - right; sp.
    - dorn IHl; destruct (deq a x); subst; tcsp.
      right; sp.
  Defined.

  Lemma deq_dset_member {p} (x : get_patom_set p) l : LIn x l [+] !(LIn x l).
  Proof.
    apply deq_member.
    destruct p; destruct patom; sp.
  Defined.

  Definition dset_member {p} (x : get_patom_set p) l :=
    match deq_dset_member x l with
      | inl _ => True
      | inr _ => False
    end.

  Lemma dset_member_proof_irrelevance {p} :
    forall (a : get_patom_set p) l (x y : dset_member a l),
      x = y.
  Proof.
    intros.
    allunfold @dset_member.
    destruct (deq_dset_member a l); tcsp.
    destruct x; destruct y; auto.
  Qed.

  Definition dset_member_eq {p} :
    forall (a : get_patom_set p) l (x : dset_member a l), Prop.
  Proof.
    intros a l x.
    unfold dset_member in x.
    destruct (deq_dset_member a l).
    exact (x = I).
    destruct x.
  Defined.

  Lemma dseq_member_eq_term {p} :
    forall (a : get_patom_set p) l (x : dset_member a l), False.
  Proof.
    intros a l x.
    (*rw @dset_member_eq in x.*)
  Abort.

  Lemma dset_member_iff {p} :
    forall (x : get_patom_set p) l, dset_member x l <=> LIn x l.
  Proof.
    introv.
    unfold dset_member.
    destruct (deq_dset_member x l); split; sp.
  Qed.

  Lemma dset_member_if {p} :
    forall (x : get_patom_set p) l, LIn x l -> dset_member x l.
  Proof.
    introv i.
    unfold dset_member.
    destruct (deq_dset_member x l); auto.
  Defined.

End ProofIrrelevantDSetMembership.




(* =============================================================== *)

Section GetUtokens.

Definition get_utokens_hyp {p} (h : @hypothesis p) : list (get_patom_set p) :=
  get_utokens (htyp h).

Definition get_utokens_bhyps {p} (hs : @bhyps p) : list (get_patom_set p) :=
  flat_map get_utokens_hyp hs.

Definition get_utokens_concl {p} (c : @conclusion p) : list (get_patom_set p) :=
  match c with
    | concl_ext ctype extract => get_utokens ctype ++ get_utokens extract
    | concl_typ ctype => get_utokens ctype
  end.

Definition get_utokens_bseq {p} (s : @baresequent p) : list (get_patom_set p) :=
  get_utokens_bhyps (hyps s) ++ get_utokens_concl (concl s).

Definition get_utokens_seq {p} (s : @sequent p) : list (get_patom_set p) :=
  get_utokens_bseq (projT1 s).

Definition get_utokens_ctseq {p} (s : @ctsequent p) : list (get_patom_set p) :=
  get_utokens_seq (projT1 s).

Definition get_utokens_cseq {p} (s : @csequent p) : list (get_patom_set p) :=
  get_utokens_ctseq (projT1 s).


Lemma in_utok_o_if_c {p} :
  forall (u : get_patom_set p) c,
    dset_member u (get_utokens_c c)
    -> dset_member u (get_utokens_o (Can c)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

(*
Lemma in_utok_o_if_en {p} :
  forall (u : get_patom_set p) en,
    dset_member u (get_utokens_en en)
    -> dset_member u (get_utokens_o (Exc en)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.
*)

(*
Lemma in_utok_o_if_nc {p} :
  forall (u : get_patom_set p) nc,
    dset_member u (get_utokens_nc nc)
    -> dset_member u (get_utokens_o (NCan nc)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.
*)

Lemma in_utok_if_o {p} :
  forall (u : get_patom_set p) o bts,
    dset_member u (get_utokens_o o)
    -> dset_member u (get_utokens (oterm o bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_if_o {p} :
  forall (u : get_patom_set p) o bs,
    dset_member u (get_utokens_o o)
    -> dset_member u (get_utokens_so (soterm o bs)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_if_bts {p} :
  forall (u : get_patom_set p) o bts,
    dset_member u (flat_map get_utokens_b bts)
    -> dset_member u (get_utokens (oterm o bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_if_bts {p} :
  forall (u : get_patom_set p) o bts,
    dset_member u (flat_map get_utokens_b_so bts)
    -> dset_member u (get_utokens_so (soterm o bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_if_ts {p} :
  forall (u : get_patom_set p) v ts,
    dset_member u (flat_map get_utokens_so ts)
    -> dset_member u (get_utokens_so (sovar v ts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_b_if_t {p} :
  forall (u : get_patom_set p) vs t,
    dset_member u (get_utokens t)
    -> dset_member u (get_utokens_b (bterm vs t)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; sp.
Qed.

Lemma in_utok_so_b_if_t {p} :
  forall (u : get_patom_set p) vs t,
    dset_member u (get_utokens_so t)
    -> dset_member u (get_utokens_b_so (sobterm vs t)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; sp.
Qed.

Lemma in_utok_bs_if_b {p} :
  forall (u : get_patom_set p) bt bts,
    dset_member u (get_utokens_b bt)
    -> dset_member u (flat_map get_utokens_b (bt :: bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_bs_if_b {p} :
  forall (u : get_patom_set p) bt bts,
    dset_member u (get_utokens_b_so bt)
    -> dset_member u (flat_map get_utokens_b_so (bt :: bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_bs_if_bs {p} :
  forall (u : get_patom_set p) bt bts,
    dset_member u (flat_map get_utokens_b bts)
    -> dset_member u (flat_map get_utokens_b (bt :: bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_ts_if_t {p} :
  forall (u : get_patom_set p) t ts,
    dset_member u (get_utokens_so t)
    -> dset_member u (flat_map get_utokens_so (t :: ts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_ts_if_ts {p} :
  forall (u : get_patom_set p) t ts,
    dset_member u (flat_map get_utokens_so ts)
    -> dset_member u (flat_map get_utokens_so (t :: ts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_ts_if_ts {p} :
  forall (u : get_patom_set p) t ts,
    dset_member u (flat_map get_utokens ts)
    -> dset_member u (flat_map get_utokens (t :: ts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_so_bs_if_bs {p} :
  forall (u : get_patom_set p) bt bts,
    dset_member u (flat_map get_utokens_b_so bts)
    -> dset_member u (flat_map get_utokens_b_so (bt :: bts)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_h_if_bhyps {p} :
  forall (u : get_patom_set p) h hs,
    dset_member u (get_utokens_hyp h)
    -> dset_member u (get_utokens_bhyps (h :: hs)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_bhyps_if_bhyps {p} :
  forall (u : get_patom_set p) h hs,
    dset_member u (get_utokens_bhyps hs)
    -> dset_member u (get_utokens_bhyps (h :: hs)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_e_if_lib {p} :
  forall (u : get_patom_set p) e es,
    dset_member u (get_utokens_library_entry e)
    -> dset_member u (get_utokens_library (e :: es)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_es_if_lib {p} :
  forall (u : get_patom_set p) e es,
    dset_member u (get_utokens_library es)
    -> dset_member u (get_utokens_library (e :: es)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_concl_ext_if_ctype {p} :
  forall (u : get_patom_set p) ctype extract,
    dset_member u (get_utokens ctype)
    -> dset_member u (get_utokens_concl (concl_ext ctype extract)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_concl_ext_if_extract {p} :
  forall (u : get_patom_set p) ctype extract,
    dset_member u (get_utokens extract)
    -> dset_member u (get_utokens_concl (concl_ext ctype extract)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_concl_typ_if_ctype {p} :
  forall (u : get_patom_set p) ctype,
    dset_member u (get_utokens ctype)
    -> dset_member u (get_utokens_concl (concl_typ ctype)).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_bseq_if_bhyps {p} :
  forall (u : get_patom_set p) s,
    dset_member u (get_utokens_bhyps (hyps s))
    -> dset_member u (get_utokens_bseq s).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma in_utok_bseq_if_concl {p} :
  forall (u : get_patom_set p) s,
    dset_member u (get_utokens_concl (concl s))
    -> dset_member u (get_utokens_bseq s).
Proof.
  introv k; allrw @dset_member_iff; allsimpl; allrw in_app_iff; sp.
Qed.

Lemma get_utokens_bhyps_snoc {p} :
  forall (h : @hypothesis p)
         (hs : list hypothesis),
    get_utokens_bhyps (snoc hs h) = get_utokens_bhyps hs ++ get_utokens_hyp h.
Proof.
  introv.
  unfold get_utokens_bhyps.
  rw flat_map_snoc; auto.
Qed.

Lemma get_utokens_bhyps_app {p} :
  forall hs1 hs2 : list (@hypothesis p),
    get_utokens_bhyps (hs1 ++ hs2) = get_utokens_bhyps hs1 ++ get_utokens_bhyps hs2.
Proof.
  introv.
  unfold get_utokens_bhyps.
  rw flat_map_app; auto.
Qed.

Lemma in_utok_h_if_bhyps_snoc {p} :
  forall (u : get_patom_set p) h hs,
    dset_member u (get_utokens_hyp h)
    -> dset_member u (get_utokens_bhyps (snoc hs h)).
Proof.
  introv k; allsimpl.
  allrw @dset_member_iff.
  rw @get_utokens_bhyps_snoc.
  rw in_app_iff; sp.
Qed.

Lemma in_utok_bhyps_if_bhyps_snoc {p} :
  forall (u : get_patom_set p) h hs,
    dset_member u (get_utokens_bhyps hs)
    -> dset_member u (get_utokens_bhyps (snoc hs h)).
Proof.
  introv k; allsimpl.
  allrw @dset_member_iff.
  rw @get_utokens_bhyps_snoc.
  rw in_app_iff; sp.
Qed.

Lemma in_utok_bhyps1_if_bhyps_app {p} :
  forall (u : get_patom_set p) hs1 hs2,
    dset_member u (get_utokens_bhyps hs1)
    -> dset_member u (get_utokens_bhyps (hs1 ++ hs2)).
Proof.
  introv k; allsimpl.
  allrw @dset_member_iff.
  rw @get_utokens_bhyps_app.
  rw in_app_iff; sp.
Qed.

Lemma in_utok_bhyps2_if_bhyps_app {p} :
  forall (u : get_patom_set p) hs1 hs2,
    dset_member u (get_utokens_bhyps hs2)
    -> dset_member u (get_utokens_bhyps (hs1 ++ hs2)).
Proof.
  introv k; allsimpl.
  allrw @dset_member_iff.
  rw @get_utokens_bhyps_app.
  rw in_app_iff; sp.
Qed.

End GetUtokens.




(* =============================================================== *)

Section TokenRenaming.

(**

  Renaming functions of unguessable tokens on terms, canonical
  operators, opids, bound terms, and lists of bound terms.

*)
Definition utok_ren {p d} (t : @NTerm p) :=
  {x : get_patom_set p & dset_member x (get_utokens t)} -> dset d.

(*
Definition utok_ren_en {p d} (c : @exc_name p) :=
  {x : get_patom_set p & dset_member x (get_utokens_en c)} -> dset d.
*)

Definition utok_ren_c {p d} (c : @CanonicalOp p) :=
  {x : get_patom_set p & dset_member x (get_utokens_c c)} -> dset d.

(*
Definition utok_ren_nc {p d} (c : @NonCanonicalOp p) :=
  {x : get_patom_set p & dset_member x (get_utokens_nc c)} -> dset d.
*)

Definition utok_ren_o {p d} (o : @Opid p) :=
  {x : get_patom_set p & dset_member x (get_utokens_o o)} -> dset d.

Definition utok_ren_b {p d} (bt : @BTerm p) :=
  {x : get_patom_set p & dset_member x (get_utokens_b bt)} -> dset d.

Definition utok_ren_bs {p d} (bts : list (@BTerm p)) :=
  {x : get_patom_set p & dset_member x (get_utokens_bs bts)} -> dset d.

Definition utok_ren_so {p d} (t : @SOTerm p) :=
  {x : get_patom_set p & dset_member x (get_utokens_so t)} -> dset d.

Definition utok_ren_so_b {p d} (bt : @SOBTerm p) :=
  {x : get_patom_set p & dset_member x (get_utokens_b_so bt)} -> dset d.

Definition utok_ren_so_bs {p d} (bts : list (@SOBTerm p)) :=
  {x : get_patom_set p & dset_member x (get_utokens_so_bs bts)} -> dset d.

Definition utok_ren_so_ts {p d} (ts : list (@SOTerm p)) :=
  {x : get_patom_set p & dset_member x (get_utokens_so_ts ts)} -> dset d.

Definition utok_ren_hyp {p d} (hyp : @hypothesis p) :=
  {x : get_patom_set p & dset_member x (get_utokens_hyp hyp)} -> dset d.

Definition utok_ren_bhyps {p d} (hs : @bhyps p) :=
  {x : get_patom_set p & dset_member x (get_utokens_bhyps hs)} -> dset d.

Definition utok_ren_concl {p d} (c : @conclusion p) :=
  {x : get_patom_set p & dset_member x (get_utokens_concl c)} -> dset d.

Definition utok_ren_bseq {p d} (s : @baresequent p) :=
  {x : get_patom_set p & dset_member x (get_utokens_bseq s)} -> dset d.

Definition utok_ren_seq {p d} (s : @sequent p) :=
  {x : get_patom_set p & dset_member x (get_utokens_seq s)} -> dset d.

Definition utok_ren_ctseq {p d} (s : @ctsequent p) :=
  {x : get_patom_set p & dset_member x (get_utokens_ctseq s)} -> dset d.

Definition utok_ren_cseq {p d} (s : @csequent p) :=
  {x : get_patom_set p & dset_member x (get_utokens_cseq s)} -> dset d.

Definition utok_ren_library_entry {p d} (e : @library_entry p) :=
  {x : get_patom_set p & dset_member x (get_utokens_library_entry e)} -> dset d.

Definition utok_ren_library {p d} (l : @library p) :=
  {x : get_patom_set p & dset_member x (get_utokens_library l)} -> dset d.


(**

  converts a [utok_ren_o] into a [utok_ren_c].

*)
Definition utok_ren_o2c {p d}
           (c : CanonicalOp)
           (s : @utok_ren_o p d (Can c)) : utok_ren_c c := s.

(*
(**

  converts a [utok_ren_o] into a [utok_ren_nc].

*)
Definition utok_ren_o2nc {p d}
           (nc : NonCanonicalOp)
           (s  : @utok_ren_o p d (NCan nc)) : utok_ren_nc nc := s.
*)

(*
(**

  converts a [utok_ren_o] into a [utok_ren_en].

*)
Definition utok_ren_o2en {p d}
           (e : exc_name)
           (s : @utok_ren_o p d (Exc e)) : utok_ren_en e := s.
*)

(**

  converts a [utok_ren] into a [utok_ren_o].

*)
Definition utok_ren_2o {p d}
           (o : Opid)
           (bts : list BTerm)
           (s : @utok_ren p d (oterm o bts)) : utok_ren_o o :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_if_o u o bts q)).


(* XXXXXXXXXXXXX *)


(**

  converts a [utok_ren] into a [utok_ren_bs].

*)
Definition utok_ren_2bs {p d}
           (o : Opid)
           (bts : list BTerm)
           (s : @utok_ren p d (oterm o bts)) : utok_ren_bs bts :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_if_bts u o bts q)).

(**

  converts a [utok_ren_b] into a [utok_ren].

*)
Definition utok_ren_b_2t {p d}
           (vs : list NVar)
           (t : NTerm)
           (s : @utok_ren_b p d (bterm vs t)) : utok_ren t :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_b_if_t u vs t q)).

(**

  converts a [utok_ren_bs] into a [utok_ren_b].

*)
Definition utok_ren_bs_2b {p d}
           (bt : BTerm)
           (bts : list BTerm)
           (s : @utok_ren_bs p d (bt :: bts)) : utok_ren_b bt :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_bs_if_b u bt bts q)).

(**

  converts a [utok_ren_bs] into a [utok_ren_bs].

*)
Definition utok_ren_bs_2bs {p d}
           (bt : BTerm)
           (bts : list BTerm)
           (s : @utok_ren_bs p d (bt :: bts)) : utok_ren_bs bts :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_bs_if_bs u bt bts q)).

(**

  converts a [utok_ren_bhyps] into a [utok_ren_hyp].

*)
Definition utok_ren_bhyps_2h {p d}
           (h : hypothesis)
           (hs : list hypothesis)
           (s : @utok_ren_bhyps p d (h :: hs)) : utok_ren_hyp h :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_h_if_bhyps u h hs q)).

(**

  converts a [utok_ren_bhyps] into a [utok_ren_bhyps].

*)
Definition utok_ren_bhyps_2bhyps {p d}
           (h : hypothesis)
           (hs : list hypothesis)
           (s : @utok_ren_bhyps p d (h :: hs)) : utok_ren_bhyps hs :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_bhyps_if_bhyps u h hs q)).

Definition utok_ren_lib_2e {p d}
           (e : library_entry)
           (es : list library_entry)
           (s : @utok_ren_library p d (e :: es)) : utok_ren_library_entry e :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_e_if_lib u e es q)).

Definition utok_ren_lib_2es {p d}
           (e : library_entry)
           (es : list library_entry)
           (s : @utok_ren_library p d (e :: es)) : utok_ren_library es :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_es_if_lib u e es q)).

(**

  converts a [utok_ren_concl] into a [utok_ren].

*)
Definition utok_ren_concle_2t {p d}
           (ctype extract : NTerm)
           (s : @utok_ren_concl p d (concl_ext ctype extract)) : utok_ren ctype :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_concl_ext_if_ctype u ctype extract q)).

(**

  converts a [utok_ren_concl] into a [utok_ren].

*)
Definition utok_ren_concle_2e {p d}
           (ctype extract : NTerm)
           (s : @utok_ren_concl p d (concl_ext ctype extract)) : utok_ren extract :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_concl_ext_if_extract u ctype extract q)).

(**

  converts a [utok_ren_concl] into a [utok_ren].

*)
Definition utok_ren_conclt_2t {p d}
           (ctype : NTerm)
           (s : @utok_ren_concl p d (concl_typ ctype)) : utok_ren ctype :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_concl_typ_if_ctype u ctype q)).

(**

  converts a [utok_ren_bseq] into a [utok_ren_bhyps].

*)
Definition utok_ren_bseq_2h {p d}
           (s : baresequent)
           (r : @utok_ren_bseq p d s) : utok_ren_bhyps (hyps s) :=
  fun x => let (u,q) := x in r (existT _ u (in_utok_bseq_if_bhyps u s q)).

(**

  converts a [utok_ren_bseq] into a [utok_ren_concl].

*)
Definition utok_ren_bseq_2c {p d}
           (s : baresequent)
           (r : @utok_ren_bseq p d s) : utok_ren_concl (concl s) :=
  fun x => let (u,q) := x in r (existT _ u (in_utok_bseq_if_concl u s q)).

(**

  converts a [utok_ren_seq] into a [utok_ren_bseq].

*)
Definition utok_ren_seq_2bseq {p d}
           (s : baresequent)
           (w : wf_sequent s)
           (r : @utok_ren_seq p d (existT _ s w)) : utok_ren_bseq s := r.

Definition utok_ren_bhyps_snoc_2bhyps {p d}
           (h : hypothesis)
           (hs : list hypothesis)
           (s : @utok_ren_bhyps p d (snoc hs h)) : utok_ren_bhyps hs :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_bhyps_if_bhyps_snoc u h hs q)).

Definition utok_ren_bhyps_snoc_2h {p d}
           (h : hypothesis)
           (hs : list hypothesis)
           (s : @utok_ren_bhyps p d (snoc hs h)) : utok_ren_hyp h :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_h_if_bhyps_snoc u h hs q)).

Definition utok_ren_bhyps_app_2bhyps1 {p d}
           (hs1 hs2 : list hypothesis)
           (s : @utok_ren_bhyps p d (hs1 ++ hs2)) : utok_ren_bhyps hs1 :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_bhyps1_if_bhyps_app u hs1 hs2 q)).

Definition utok_ren_bhyps_app_2bhyps2 {p d}
           (hs1 hs2 : list hypothesis)
           (s : @utok_ren_bhyps p d (hs1 ++ hs2)) : utok_ren_bhyps hs2 :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_bhyps2_if_bhyps_app u hs1 hs2 q)).

Definition utok_ren_so_bs_2b {p d}
           (bt : SOBTerm)
           (bts : list SOBTerm)
           (s : @utok_ren_so_bs p d (bt :: bts)) : utok_ren_so_b bt :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_bs_if_b u bt bts q)).

Definition utok_ren_so_bs_2bs {p d}
           (bt : SOBTerm)
           (bts : list SOBTerm)
           (s : @utok_ren_so_bs p d (bt :: bts)) : utok_ren_so_bs bts :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_bs_if_bs u bt bts q)).

Definition utok_ren_so_2bs {p d}
           (o : Opid)
           (bts : list SOBTerm)
           (s : @utok_ren_so p d (soterm o bts)) : utok_ren_so_bs bts :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_if_bts u o bts q)).

Definition utok_ren_so_2ts {p d}
           (v : NVar)
           (ts : list SOTerm)
           (s : @utok_ren_so p d (sovar v ts)) : utok_ren_so_ts ts :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_if_ts u v ts q)).

Definition utok_ren_so_ts_2t {p d}
           (t : SOTerm)
           (ts : list SOTerm)
           (s : @utok_ren_so_ts p d (t :: ts)) : utok_ren_so t :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_ts_if_t u t ts q)).

Definition utok_ren_so_ts_2ts {p d}
           (t : SOTerm)
           (ts : list SOTerm)
           (s : @utok_ren_so_ts p d (t :: ts)) : utok_ren_so_ts ts :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_ts_if_ts u t ts q)).

Definition utok_ren_so_2o {p d}
           (o : Opid)
           (bs : list SOBTerm)
           (s : @utok_ren_so p d (soterm o bs)) : utok_ren_o o :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_if_o u o bs q)).

Definition utok_ren_so_b_2t {p d}
           (vs : list NVar)
           (t : SOTerm)
           (s : @utok_ren_so_b p d (sobterm vs t)) : utok_ren_so t :=
  fun x => let (u,q) := x in s (existT _ u (in_utok_so_b_if_t u vs t q)).

End TokenRenaming.





(* =============================================================== *)

Ltac clear_eq_l x :=
  match goal with
    | [ H : x = _ |- _ ] => clear H
  end.

Ltac gen_in_utok_step :=
  let h := fresh "h" in
  match goal with
    | [ |- context[@in_utok_h_if_bhyps ?p ?a ?b ?c ?d] ]          => remember (@in_utok_h_if_bhyps p a b c d) as h;          clear_eq_l h
    | [ |- context[@in_utok_h_if_bhyps_snoc ?p ?a ?b ?c ?d] ]     => remember (@in_utok_h_if_bhyps_snoc p a b c d) as h;     clear_eq_l h
    | [ |- context[@in_utok_bhyps_if_bhyps ?p ?a ?b ?c ?d] ]      => remember (@in_utok_bhyps_if_bhyps p a b c d) as h;      clear_eq_l h
    | [ |- context[@in_utok_bhyps_if_bhyps_snoc ?p ?a ?b ?c ?d] ] => remember (@in_utok_bhyps_if_bhyps_snoc p a b c d) as h; clear_eq_l h
    | [ |- context[@in_utok_bhyps1_if_bhyps_app ?p ?a ?b ?c ?d] ] => remember (@in_utok_bhyps1_if_bhyps_app p a b c d) as h; clear_eq_l h
    | [ |- context[@in_utok_bhyps2_if_bhyps_app ?p ?a ?b ?c ?d] ] => remember (@in_utok_bhyps2_if_bhyps_app p a b c d) as h; clear_eq_l h
    | [ |- context[@in_utok_bs_if_b ?p ?a ?b ?c ?d] ]             => remember (@in_utok_bs_if_b p a b c d) as h;             clear_eq_l h
    | [ |- context[@in_utok_bs_if_bs ?p ?a ?b ?c ?d] ]            => remember (@in_utok_bs_if_bs p a b c d) as h;            clear_eq_l h
  end.

Ltac gen_in_utok := repeat gen_in_utok_step.

Ltac PI2 :=
  repeat (first
            [ progress clear_irr
            | progress proof_irr
            | progress PI
            | match goal with
                | [ H1 : dset_member ?a ?l, H2 : dset_member ?a ?l |- _ ] => assert (H2 = H1) by apply dset_member_proof_irrelevance; subst
              end
            | complete auto
         ]).




(* =============================================================== *)

Section TokenReplacing.

Lemma in_utok_c {p} :
  forall u : get_patom_set p,
    dset_member u (get_utokens_c (NUTok u)).
Proof.
  introv; rw @dset_member_iff.
  simpl; sp.
Qed.

Definition app_utok_c {p d}
           (u : get_patom_set p)
           (s : @utok_ren_c p d (NUTok u)) : dset d :=
  s (existT _ u (in_utok_c u)).

Definition replace_can {p d} (c : @CanonicalOp p) : @utok_ren_c p d c -> @CanonicalOp (set_patom p d) :=
  match c with
  | NUTok u        => fun s => @NUTok (set_patom p d) (@app_utok_c p d u s)
  | NConstP x      => fun _ => @NConstP (set_patom p d) x
  | NConstT x      => fun _ => @NConstT (set_patom p d) x
  | NLambda        => fun _ => NLambda
  | NAxiom         => fun _ => NAxiom
  | NInj x         => fun _ => NInj x
  | NPair          => fun _ => NPair
  | NSup           => fun _ => NSup
  | NRefl          => fun _ => NRefl
  | Nint i         => fun _ => Nint i
  | Nseq s         => fun _ => Nseq s
  | NUni i         => fun _ => NUni i
  | NTok t         => fun _ => NTok t
  | NEquality      => fun _ => NEquality
  | NREquality     => fun _ => NREquality
  | NFreeFromAtom  => fun _ => NFreeFromAtom
  | NEFreeFromAtom => fun _ => NEFreeFromAtom
  | NFreeFromAtoms => fun _ => NFreeFromAtoms
  | NTEquality     => fun _ => NTEquality
  | NInt           => fun _ => NInt
  | NBase          => fun _ => NBase
  | NAtom          => fun _ => NAtom
  | NUAtom         => fun _ => NUAtom
  | NFunction      => fun _ => NFunction
  | NProduct       => fun _ => NProduct
  | NSet           => fun _ => NSet
  | NTUnion        => fun _ => NTUnion
  | NIsect         => fun _ => NIsect
  | NDIsect        => fun _ => NDIsect
  | NEIsect        => fun _ => NEIsect
  | NW             => fun _ => NW
  | NM             => fun _ => NM
  | NPW            => fun _ => NPW
  | NPM            => fun _ => NPM
  | NEPertype      => fun _ => NEPertype
  | NIPertype      => fun _ => NIPertype
  | NSPertype      => fun _ => NSPertype
  | NPartial       => fun _ => NPartial
  | NTExc          => fun _ => NTExc
  | NUnion         => fun _ => NUnion
  | NEUnion        => fun _ => NEUnion
  | NUnion2        => fun _ => NUnion2
  | NApprox        => fun _ => NApprox
  | NCequiv        => fun _ => NCequiv
  | NCompute       => fun _ => NCompute
  | NRec           => fun _ => NRec
  | NImage         => fun _ => NImage
  | NQuotient      => fun _ => NQuotient
  | NAdmiss        => fun _ => NAdmiss
  | NMono          => fun _ => NMono
  | NOmega         => fun _ => NOmega
  end.

(*
Definition replace_exc_name {p d} (en : @exc_name p) : @utok_ren_en p d en -> @exc_name (set_patom p d) :=
  match en with
  | Some a => fun s => Some (@app_utok_c p d a s)
  | None => fun s => None
  end.
*)

(*
Definition replace_ncan {p d} (nc : @NonCanonicalOp p) : @utok_ren_nc p d nc -> @NonCanonicalOp (set_patom p d) :=
  match nc with
    | NApply      => fun s => NApply
    | NFix        => fun s => NFix
    | NSpread     => fun s => NSpread
    | NDsup       => fun s => NDsup
    | NDecide     => fun s => NDecide
    | NCbv        => fun s => NCbv
    | NSleep      => fun s => NSleep
    | NTUni       => fun s => NTUni
    | NMinus      => fun s => NMinus
    | NTryCatch e => fun s => NTryCatch (replace_exc_name e s)
    | NCompOp c   => fun s => NCompOp c
    | NArithOp c  => fun s => NArithOp c
    | NCanTest c  => fun s => NCanTest c
  end.
*)

Definition replace_opid {p d} (o : @Opid p) : @utok_ren_o p d o -> @Opid (set_patom p d) :=
  match o with
    | Can c   => fun s => Can (@replace_can p d c (utok_ren_o2c c s))
    | NCan nc => fun s => NCan nc
    | Exc     => fun s => Exc
    | Abs x   => fun _ => Abs x
  end.

Lemma zip_ren_ext {p d} :
  forall (bt : @BTerm p) bs,
    list {b : BTerm $ @utok_ren_b p d b # LIn b bs}
    -> list {b : BTerm $ @utok_ren_b p d b # LIn b (bt :: bs)}.
Proof.
  introv l.
  induction l.
  exact [].
  exrepnd.
  exact ((existT (fun b => @utok_ren_b p d b # LIn b (bt :: bs)) b (a1,in_cons_if b bt bs a0))
           :: IHl).
Defined.

Fixpoint zip_ren_bterms {p d} (bts : list BTerm) :
  @utok_ren_bs p d bts
  -> list {b : @BTerm p & @utok_ren_b p d b} :=
  match bts with
    | [] => fun _ => []
    | bt :: bs =>
      fun s =>
        let s1 := @utok_ren_bs_2b p d bt bs s in
        let s2 := @utok_ren_bs_2bs p d bt bs s in
        (existT (fun b => @utok_ren_b p d b) bt s1)
          :: (zip_ren_bterms bs s2)
  end.

Fixpoint zip_ren_bterms' {p d} (bts : list BTerm) :
  @utok_ren_bs p d bts
  -> list {b : @BTerm p & @utok_ren_b p d b # LIn b bts} :=
  match bts with
    | [] => fun _ => []
    | bt :: bs =>
      fun s =>
        let s1 := @utok_ren_bs_2b p d bt bs s in
        let s2 := @utok_ren_bs_2bs p d bt bs s in
        (existT (fun b => @utok_ren_b p d b # LIn b (bt :: bs)) bt (s1,in_cons_left bt bs))
          :: (zip_ren_ext bt bs (zip_ren_bterms' bs s2))
  end.

(*
Require Import Program.

(**

  Let us now define a function that takes a term and a renaming of
  its unguessable atoms and applies the renaming.  Here is a solution
  that uses [Program Fixpoint].  We present below another version that
  does not uses [Program Fixpoint], but [Fixpoint] along with a raw
  [fix].

 *)
Program Fixpoint replace_utokens' {p d} (t : @NTerm p) {measure (size t)} :
  @utok_ren p d t -> @NTerm (set_patom p d) :=
  match t with
    | vterm v => fun _ => vterm v
    | oterm o bts =>
      fun s =>
        oterm (replace_opid o (utok_ren_2o o bts s))
              (map (fun (x : {b : @BTerm p & @utok_ren_b p d b # LIn b bts}) =>
                      let (bt,y) := x in
                      (match bt return @utok_ren_b p d bt # LIn bt bts -> @BTerm (set_patom p d) with
                         | bterm vs t =>
                           fun s =>
                             bterm vs (replace_utokens' t _ (*(utok_ren_b_2t vs t (fst s))*))
                       end) y)
                   (zip_ren_bterms' bts (utok_ren_2bs o bts s)))
  end.
Obligation 1.
simpl; apply (size_subterm2 o) in l; simpl in l; auto.
Qed.
Obligation 2.
exact (utok_ren_b_2t vs t0 u).
Qed.
 *)

(*
(* This is not accepted *)
Fixpoint replace_utokens_t {p d} (t : @NTerm p) :
  @utok_ren p d t -> @NTerm (set_patom p d) :=
  match t with
    | vterm v => fun _ => vterm v
    | oterm o bts =>
      fun s =>
        oterm (replace_opid o (utok_ren_2o o bts s))
              (map (fun (x : {b : @BTerm p & @utok_ren_b p d b}) =>
                      let (bt,y) := x in replace_utokens_b bt y)
                   (zip_ren_bterms bts (utok_ren_2bs o bts s)))
  end
with replace_utokens_b {p d} (bt : @BTerm p) :
       @utok_ren_b p d bt -> @BTerm (set_patom p d) :=
       match bt with
         | bterm vs t =>
           fun s =>
             bterm vs (@replace_utokens_t p d t (@utok_ren_b_2t p d vs t s))
       end.
*)

Lemma noutokens_sterm_app {o} :
  forall (f : @ntseq o) n,
    wf_term (sterm f) -> noutokens (f n).
Proof.
  introv wf.
  apply wf_term_eq in wf.
  rw @nt_wf_sterm_iff in wf.
  pose proof (wf n) as q; clear wf; repnd; auto.
Qed.

Lemma wf_term_sterm_app {o} :
  forall (f : @ntseq o) n,
    wf_term (sterm f) -> wf_term (f n).
Proof.
  introv wf.
  allrw @wf_term_eq.
  rw @nt_wf_sterm_iff in wf.
  pose proof (wf n) as q; clear wf; repnd; auto.
Qed.

Definition noutokens_o {o} (op : @Opid o) :=
  get_utokens_o op = [].

Definition noutokens_c {o} (c : @CanonicalOp o) :=
  get_utokens_c c = [].


Definition set_patom_noutokens_c {p d} (c : @CanonicalOp p) :
  noutokens_c c -> @CanonicalOp (set_patom p d) :=
  match c with
  | NUTok u        => fun nu : [u] = [] => match nu with end
  | NConstP x      => fun _ => @NConstP (set_patom p d) x
  | NConstT x      => fun _ => @NConstT (set_patom p d) x
  | NLambda        => fun _ => NLambda
  | NAxiom         => fun _ => NAxiom
  | NInj x         => fun _ => NInj x
  | NPair          => fun _ => NPair
  | NSup           => fun _ => NSup
  | NRefl          => fun _ => NRefl
  | Nint i         => fun _ => Nint i
  | Nseq s         => fun _ => Nseq s
  | NUni i         => fun _ => NUni i
  | NTok t         => fun _ => NTok t
  | NEquality      => fun _ => NEquality
  | NREquality     => fun _ => NREquality
  | NFreeFromAtom  => fun _ => NFreeFromAtom
  | NEFreeFromAtom => fun _ => NEFreeFromAtom
  | NFreeFromAtoms => fun _ => NFreeFromAtoms
  | NTEquality     => fun _ => NTEquality
  | NInt           => fun _ => NInt
  | NBase          => fun _ => NBase
  | NAtom          => fun _ => NAtom
  | NUAtom         => fun _ => NUAtom
  | NFunction      => fun _ => NFunction
  | NProduct       => fun _ => NProduct
  | NSet           => fun _ => NSet
  | NTUnion        => fun _ => NTUnion
  | NIsect         => fun _ => NIsect
  | NDIsect        => fun _ => NDIsect
  | NEIsect        => fun _ => NEIsect
  | NW             => fun _ => NW
  | NM             => fun _ => NM
  | NPW            => fun _ => NPW
  | NPM            => fun _ => NPM
  | NEPertype      => fun _ => NEPertype
  | NIPertype      => fun _ => NIPertype
  | NSPertype      => fun _ => NSPertype
  | NPartial       => fun _ => NPartial
  | NTExc          => fun _ => NTExc
  | NUnion         => fun _ => NUnion
  | NEUnion        => fun _ => NEUnion
  | NUnion2        => fun _ => NUnion2
  | NApprox        => fun _ => NApprox
  | NCequiv        => fun _ => NCequiv
  | NCompute       => fun _ => NCompute
  | NRec           => fun _ => NRec
  | NImage         => fun _ => NImage
  | NQuotient      => fun _ => NQuotient
  | NAdmiss        => fun _ => NAdmiss
  | NMono          => fun _ => NMono
  | NOmega         => fun _ => NOmega
  end.

Lemma noutokens_o2c {o} :
  forall (c : @CanonicalOp o), noutokens_o (Can c) -> noutokens_c c.
Proof.
  auto.
Qed.

Definition set_patom_noutokens_o {p d} (op : @Opid p) :
  noutokens_o op -> @Opid (set_patom p d) :=
  match op with
  | Can c   => fun nu => Can (set_patom_noutokens_c c (noutokens_o2c c nu))
  | NCan nc => fun _ => NCan nc
  | Exc     => fun _ => Exc
  | Abs abs => fun _ => Abs abs
  end.

Lemma noutokens_2o {o} :
  forall (op : @Opid o) bs, noutokens (oterm op bs) -> noutokens_o op.
Proof.
  introv no.
  allunfold @noutokens; allsimpl.
  allrw @app_eq_nil_iff; repnd; auto.
Qed.

Definition noutokens_b {o} (b : @BTerm o) :=
  get_utokens_b b = [].

Definition noutokens_bs {o} (bs : list (@BTerm o)) :=
  get_utokens_bs bs = [].

Lemma noutokens_2bs {o} :
  forall (op : @Opid o) bs, noutokens (oterm op bs) -> noutokens_bs bs.
Proof.
  introv no.
  allunfold @noutokens; allsimpl.
  allrw @app_eq_nil_iff; repnd; auto.
Qed.

Lemma noutokens_bs2b {o} :
  forall (b : @BTerm o) bs, noutokens_bs (b :: bs) -> noutokens_b b.
Proof.
  introv no.
  allunfold @noutokens_bs; allsimpl.
  allrw @app_eq_nil_iff; repnd; auto.
Qed.

Lemma noutokens_bs2bs {o} :
  forall (b : @BTerm o) bs, noutokens_bs (b :: bs) -> noutokens_bs bs.
Proof.
  introv no.
  allunfold @noutokens_bs; allsimpl.
  allrw @app_eq_nil_iff; repnd; auto.
Qed.

Lemma wf_term_2bs {o} :
  forall (op : @Opid o) bs, wf_term (oterm op bs) -> wf_bterms bs.
Proof.
  introv w.
  allrw @wf_oterm_iff; repnd; auto.
Qed.

Lemma wf_bterms_2b {o} :
  forall b (bs : list (@BTerm o)), wf_bterms (b :: bs) -> wf_bterm b.
Proof.
  introv w.
  unfold wf_bterms in w; allsimpl.
  apply w; tcsp.
Qed.

Lemma wf_bterms_2bs {o} :
  forall b (bs : list (@BTerm o)), wf_bterms (b :: bs) -> wf_bterms bs.
Proof.
  introv w.
  unfold wf_bterms in w; allsimpl.
  introv i; apply w; tcsp.
Qed.

Lemma wf_bterm_2t {o} :
  forall vs (t : @NTerm o), wf_bterm (bterm vs t) -> wf_term t.
Proof.
  introv w.
  allrw @wf_bterm_iff; auto.
Qed.

Definition wf_sobterms {o} (bs : list (@SOBTerm o)) :=
  forall b : SOBTerm, LIn b bs -> wf_sobterm b.

Definition wf_soterms {o} (ts : list (@SOTerm o)) :=
  forall t : SOTerm, LIn t ts -> wf_soterm t.

Lemma wf_soterm_2bs {o} :
  forall (op : @Opid o) bs, wf_soterm (soterm op bs) -> wf_sobterms bs.
Proof.
  introv w.
  allrw @wf_soterm_iff; repnd; auto.
  introv i.
  destruct b.
  apply (w l); auto.
Qed.

Lemma wf_soterms_2t {o} :
  forall (t : @SOTerm o) ts, wf_soterms (t :: ts) -> wf_soterm t.
Proof.
  introv w.
  unfold wf_soterms in w; allsimpl.
  apply w; auto.
Qed.

Lemma wf_soterms_2ts {o} :
  forall (t : @SOTerm o) ts, wf_soterms (t :: ts) -> wf_soterms ts.
Proof.
  introv w i.
  unfold wf_soterms in w; allsimpl.
  apply w; auto.
Qed.

Lemma wf_sobterms_2b {o} :
  forall (b : @SOBTerm o) bs, wf_sobterms (b :: bs) -> wf_sobterm b.
Proof.
  introv w.
  unfold wf_sobterms in w; allsimpl.
  apply w; auto.
Qed.

Lemma wf_sobterms_2bs {o} :
  forall (b : @SOBTerm o) bs, wf_sobterms (b :: bs) -> wf_sobterms bs.
Proof.
  introv w i.
  unfold wf_sobterms in w; allsimpl.
  apply w; auto.
Qed.

Lemma wf_sobterm_2t {o} :
  forall vs (t : @SOTerm o), wf_sobterm (sobterm vs t) -> wf_soterm t.
Proof.
  introv w.
  unfold wf_sobterm in w; allsimpl.
  unfold wf_soterm.
  rw @wf_bterm_iff in w; auto.
Qed.

Lemma wf_sovar_2ts {o} :
  forall v (ts : list (@SOTerm o)), wf_soterm (sovar v ts) -> wf_soterms ts.
Proof.
  introv w.
  rw @wf_sovar in w; auto.
Qed.

Lemma wf_soterms_2sovar {o} :
  forall v (ts : list (@SOTerm o)), wf_soterms ts -> wf_soterm (sovar v ts).
Proof.
  introv w.
  apply @wf_sovar; auto.
Qed.

Lemma wf_soseq_2t {o} :
  forall (f : @ntseq o) n, wf_soterm (soseq f) -> wf_term (f n).
Proof.
  introv w.
  unfold wf_soterm in w; allsimpl.
  apply wf_term_sterm_app; auto.
Qed.

Lemma noutokens_b2t {o} :
  forall vs (t : @NTerm o), noutokens_b (bterm vs t) -> noutokens t.
Proof.
  introv w.
  allunfold @noutokens_b; allsimpl; auto.
Qed.

Fixpoint set_patom_noutokens {p d} (t : @NTerm p) :
  noutokens t -> wf_term t -> @NTerm (set_patom p d) :=
  match t with
  | vterm v => fun _ _ => vterm v
  | sterm f =>
    fun _ wf =>
      sterm (fun n => set_patom_noutokens
                        (f n)
                        (noutokens_sterm_app f n wf)
                        (wf_term_sterm_app f n wf))
  | oterm op bs =>
    fun nu wf =>
      oterm (set_patom_noutokens_o op (noutokens_2o op bs nu))
            ((fix F (bs : list (@BTerm p)) :
                noutokens_bs bs
                -> wf_bterms bs
                -> list (@BTerm (set_patom p d)) :=
                match bs with
                | [] => fun _ _ => []
                | b :: bs =>
                  fun nu wf =>
                    (set_patom_noutokens_b b (noutokens_bs2b b bs nu) (wf_bterms_2b b bs wf))
                      :: (F bs (noutokens_bs2bs b bs nu) (wf_bterms_2bs b bs wf))
                end) bs (noutokens_2bs op bs nu) (wf_term_2bs op bs wf))
  end
with set_patom_noutokens_b {p d} (b : @BTerm p) :
       noutokens_b b -> wf_bterm b -> @BTerm (set_patom p d) :=
       match b with
         | bterm vs t =>
           fun nu wf =>
             bterm vs (@set_patom_noutokens
                         p d t
                         (noutokens_b2t vs t nu)
                         (wf_bterm_2t vs t wf))
       end.

Definition set_patom_noutokens_ntseq {p d} (f : @ntseq p) :
  wf_term (sterm f) -> @ntseq (set_patom p d) :=
  fun w n => set_patom_noutokens
               (f n)
               (noutokens_sterm_app f n w)
               (wf_term_sterm_app f n w).

Fixpoint replace_utokens_t {p d} (t : @NTerm p) :
  wf_term t -> @utok_ren p d t -> @NTerm (set_patom p d) :=
  match t with
  | vterm v => fun _ _ => vterm v
  | sterm f => fun w _ => @set_patom_noutokens p d (sterm f) eq_refl w
  | oterm o bts =>
    fun w s =>
      oterm (replace_opid o (utok_ren_2o o bts s))
            ((fix F (bts : list (@BTerm p)) :
                wf_bterms bts -> @utok_ren_bs p d bts -> list (@BTerm (set_patom p d)) :=
                match bts with
                | [] => fun _ _ => []
                | bt :: bs =>
                  fun w s =>
                    (replace_utokens_b bt (wf_bterms_2b bt bs w) (@utok_ren_bs_2b p d bt bs s))
                      :: (F bs (wf_bterms_2bs bt bs w) (@utok_ren_bs_2bs p d bt bs s))
                end) bts (wf_term_2bs o bts w) (utok_ren_2bs o bts s))
  end
with replace_utokens_b {p d} (bt : @BTerm p) :
       wf_bterm bt -> @utok_ren_b p d bt -> @BTerm (set_patom p d) :=
       match bt with
       | bterm vs t =>
         fun w s =>
           bterm vs (@replace_utokens_t p d t (wf_bterm_2t vs t w) (@utok_ren_b_2t p d vs t s))
       end.

Fixpoint replace_utokens_so {p d} (t : @SOTerm p) :
  wf_soterm t -> @utok_ren_so p d t -> @SOTerm (set_patom p d) :=
  match t with
    | sovar v ts =>
      fun w s =>
        sovar
          v
          ((fix F (ts : list (@SOTerm p)) :
              wf_soterms ts -> @utok_ren_so_ts p d ts -> list (@SOTerm (set_patom p d)) :=
              match ts with
                | [] => fun _ _ => []
                | t :: ts =>
                  fun w s =>
                    (replace_utokens_so t (wf_soterms_2t t ts w) (@utok_ren_so_ts_2t p d t ts s))
                      :: (F ts (wf_soterms_2ts t ts w) (@utok_ren_so_ts_2ts p d t ts s))
              end) ts (wf_sovar_2ts v ts w) (utok_ren_so_2ts v ts s))
    | soseq f =>
      fun w _ => soseq (set_patom_noutokens_ntseq f w)
    | soterm o bs =>
      fun w s =>
        soterm (replace_opid o (utok_ren_so_2o o bs s))
               ((fix F (bs : list (@SOBTerm p)) :
                   wf_sobterms bs -> @utok_ren_so_bs p d bs -> list (@SOBTerm (set_patom p d)) :=
                   match bs with
                     | [] => fun _ _ => []
                     | b :: bs =>
                       fun w s =>
                         (replace_utokens_so_b b (wf_sobterms_2b b bs w) (@utok_ren_so_bs_2b p d b bs s))
                           :: (F bs (wf_sobterms_2bs b bs w) (@utok_ren_so_bs_2bs p d b bs s))
                   end) bs (wf_soterm_2bs o bs w) (utok_ren_so_2bs o bs s))
  end
with replace_utokens_so_b {p d} (b : @SOBTerm p) :
       wf_sobterm b -> @utok_ren_so_b p d b -> @SOBTerm (set_patom p d) :=
       match b with
         | sobterm vs t =>
           fun w s =>
             sobterm vs (@replace_utokens_so
                           p d t
                           (wf_sobterm_2t vs t w)
                           (@utok_ren_so_b_2t p d vs t s))
       end.

Definition replace_utokens_hyp {p d}
           (h : @hypothesis p)
           (w : wf_term (htyp h))
           (r : @utok_ren_hyp p d h) :
  @hypothesis (set_patom p d) :=
  {|
    hvar   := hvar h ;
    hidden := hidden h;
    htyp   := replace_utokens_t (htyp h) w r;
    lvl    := lvl h
  |}.

Lemma wf_hyps_2h {o} :
  forall h (hs : @bhyps o), wf_hyps (h :: hs) -> wf_hyp h.
Proof.
  introv wf.
  allrw @wf_hyps_cons; sp.
Qed.

Lemma wf_hyps_2hs {o} :
  forall h (hs : @bhyps o), wf_hyps (h :: hs) -> wf_hyps hs.
Proof.
  introv wf.
  allrw @wf_hyps_cons; sp.
Qed.

Fixpoint replace_utokens_bhyps {p d}
         (hs : @bhyps p) :
  wf_hyps hs -> @utok_ren_bhyps p d hs -> @bhyps (set_patom p d) :=
  match hs with
    | [] => fun _ _ => []
    | h :: hs =>
      fun w r =>
        (replace_utokens_hyp h (wf_hyps_2h h hs w) (utok_ren_bhyps_2h h hs r))
          :: (replace_utokens_bhyps hs (wf_hyps_2hs h hs w) (utok_ren_bhyps_2bhyps h hs r))
  end.

Lemma wf_concl_ext_2typ {o} :
  forall (t e : @NTerm o),
    wf_concl (concl_ext t e) -> wf_term t.
Proof.
  introv wf; unfold wf_concl in wf; allsimpl; sp.
Qed.

Lemma wf_concl_ext_2ext {o} :
  forall (t e : @NTerm o),
    wf_concl (concl_ext t e) -> wf_term e.
Proof.
  introv wf; unfold wf_concl in wf; allsimpl; sp.
Qed.

Lemma wf_concl_typ_2typ {o} :
  forall (t : @NTerm o),
    wf_concl (concl_typ t) -> wf_term t.
Proof.
  introv wf; unfold wf_concl in wf; allsimpl; sp.
Qed.

Definition replace_utokens_concl {p d}
           (c : @conclusion p) :
  wf_concl c -> @utok_ren_concl p d c -> @conclusion (set_patom p d) :=
  match c with
    | concl_ext t e =>
      fun w s =>
        concl_ext
          (replace_utokens_t
             t
             (wf_concl_ext_2typ t e w)
             (utok_ren_concle_2t t e s))
          (replace_utokens_t
             e
             (wf_concl_ext_2ext t e w)
             (utok_ren_concle_2e t e s))
    | concl_typ t =>
      fun w s =>
        concl_typ (replace_utokens_t t (wf_concl_typ_2typ t w) s)
  end.

Lemma wf_sequent_2hyps {o} :
  forall (s : @baresequent o), wf_sequent s -> wf_hyps (hyps s).
Proof.
  introv wf.
  destruct s; allsimpl.
  unfold wf_sequent in wf; repnd; allsimpl.
  apply wf_hypotheses_implies_wf_hyps; auto.
Qed.

Lemma wf_sequent_2concl {o} :
  forall (s : @baresequent o), wf_sequent s -> wf_concl (concl s).
Proof.
  introv wf.
  destruct s; allsimpl.
  unfold wf_sequent in wf; repnd; allsimpl; auto.
Qed.

Definition replace_utokens_bseq {p d}
           (s : @baresequent p)
           (w : wf_sequent s)
           (r : @utok_ren_bseq p d s) : @baresequent (set_patom p d) :=
  {|
    hyps  := replace_utokens_bhyps (hyps s) (wf_sequent_2hyps s w) (utok_ren_bseq_2h s r);
    concl := replace_utokens_concl (concl s) (wf_sequent_2concl s w) (utok_ren_bseq_2c s r)
  |}.

(*
Lemma utok_ren_bhyps_cons {p d} :
  forall h hs,
    @utok_ren_hyp p d h
    -> @utok_ren_bhyps p d hs
    -> @utok_ren_bhyps p d (h :: hs).
Proof.
  introv.
  unfold utok_ren_hyp, utok_ren_bhyps; introv k1 k2 k3; exrepnd; allsimpl.
  apply in_app_iff in k0; dorn k0.
  apply k1; exists x; sp.
  apply k2; exists x; sp.
Defined.
*)

Definition eq_utok_ren_c {p d} c (r1 r2 : @utok_ren_c p d c) :=
  forall x, r1 x = r2 x.

(*
Definition eq_utok_ren_en {p d} en (r1 r2 : @utok_ren_en p d en) :=
  forall x, r1 x = r2 x.
*)

(*
Definition eq_utok_ren_nc {p d} nc (r1 r2 : @utok_ren_nc p d nc) :=
  forall x, r1 x = r2 x.
*)

Definition eq_utok_ren_o {p d} o (r1 r2 : @utok_ren_o p d o) :=
  forall x, r1 x = r2 x.

Definition eq_utok_ren {p d} t (r1 r2 : @utok_ren p d t) :=
  forall x, r1 x = r2 x.

Definition eq_utok_ren_bs {p d} bs (r1 r2 : @utok_ren_bs p d bs) :=
  forall x, r1 x = r2 x.

Definition eq_utok_ren_hyp {p d} h (r1 r2 : @utok_ren_hyp p d h) :=
  forall x, r1 x = r2 x.

Definition eq_utok_ren_bhyps {p d} hs (r1 r2 : @utok_ren_bhyps p d hs) :=
  forall x, r1 x = r2 x.

Definition eq_utok_ren_concl {p d} hs (r1 r2 : @utok_ren_concl p d hs) :=
  forall x, r1 x = r2 x.

Definition eq_utok_ren_bseq {p d} hs (r1 r2 : @utok_ren_bseq p d hs) :=
  forall x, r1 x = r2 x.

Lemma eq_utok_ren_hyp_implies_t {p d} :
  forall hvar hidden htyp lvl r1 r2,
    @eq_utok_ren_hyp
      p d
      {| hvar := hvar; hidden := hidden; htyp := htyp; lvl := lvl |}
      r1 r2
    -> eq_utok_ren htyp r1 r2.
Proof.
  auto.
Qed.

Lemma eq_utok_ren_implies_o {p d} :
  forall o bts r1 r2,
    @eq_utok_ren
      p d
      (oterm o bts)
      r1 r2
    -> eq_utok_ren_o o (utok_ren_2o o bts r1) (utok_ren_2o o bts r2).
Proof.
  introv e; introv; exrepnd.
  unfold eq_utok_ren in e.
  pose proof (e (existT _ x0 (in_utok_if_o x0 o bts x1))); auto.
Qed.

Lemma eq_utok_ren_implies_bs {p d} :
  forall o bts r1 r2,
    @eq_utok_ren
      p d
      (oterm o bts)
      r1 r2
    -> eq_utok_ren_bs bts (utok_ren_2bs o bts r1) (utok_ren_2bs o bts r2).
Proof.
  introv e; introv; exrepnd.
  unfold eq_utok_ren in e.
  pose proof (e (existT _ x0 (in_utok_if_bts x0 o bts x1))); auto.
Qed.

Lemma eq_utok_ren_o_implies_c {p d} :
  forall c r1 r2,
    @eq_utok_ren_o p d (Can c) r1 r2
    -> eq_utok_ren_c c (utok_ren_o2c c r1) (utok_ren_o2c c r2).
Proof.
  introv e; introv; exrepnd.
  unfold eq_utok_ren_o in e.
  pose proof (e (existT _ x0 (in_utok_o_if_c x0 c x1))); auto.
Qed.

(*
Lemma eq_utok_ren_o_implies_e {p d} :
  forall e r1 r2,
    @eq_utok_ren_o p d (Exc e) r1 r2
    -> eq_utok_ren_en e (utok_ren_o2en e r1) (utok_ren_o2en e r2).
Proof.
  introv x; introv; exrepnd.
  unfold eq_utok_ren_o in x.
  pose proof (x (existT _ x1 (in_utok_o_if_en x1 e x2))); auto.
Qed.
*)

(*
Lemma eq_utok_ren_o_implies_nc {p d} :
  forall nc r1 r2,
    @eq_utok_ren_o p d (NCan nc) r1 r2
    -> eq_utok_ren_nc nc (utok_ren_o2nc nc r1) (utok_ren_o2nc nc r2).
Proof.
  introv e; introv; exrepnd.
  unfold eq_utok_ren_o in e.
  pose proof (e (existT _ x0 (in_utok_o_if_nc x0 nc x1))); auto.
Qed.
*)

Lemma eq_utok_ren_bs_cons_implies_bs {p d} :
  forall b bs (r1 r2 : @utok_ren_bs p d (b :: bs)),
    eq_utok_ren_bs (b :: bs) r1 r2
    -> eq_utok_ren_bs bs (utok_ren_bs_2bs b bs r1) (utok_ren_bs_2bs b bs r2).
Proof.
  introv e; introv; exrepnd.
  pose proof (e (existT _ x0 (in_utok_bs_if_bs x0 b bs x1))); auto.
Qed.

Lemma replace_can_eq {p d} :
  forall c (r1 r2 : @utok_ren_c p d c),
    eq_utok_ren_c c r1 r2
    -> replace_can c r1 = replace_can c r2.
Proof.
  destruct c; introv e; simpl; auto.
  unfold eq_utok_ren_c in e.
  unfold app_utok_c.
  rw e; auto.
Qed.

(*
Lemma replace_ncan_eq {p d} :
  forall nc (r1 r2 : @utok_ren_nc p d nc),
    eq_utok_ren_nc nc r1 r2
    -> replace_ncan nc r1 = replace_ncan nc r2.
Proof.
  destruct nc; introv x; simpl; auto.
  unfold eq_utok_ren_nc in x.
  f_equal.
  unfold replace_exc_name.
  destruct e; auto.
  unfold app_utok_c.
  rw x; auto.
Qed.
*)

(*
Lemma replace_exc_eq {p d} :
  forall en (r1 r2 : @utok_ren_en p d en),
    eq_utok_ren_en en r1 r2
    -> replace_exc_name en r1 = replace_exc_name en r2.
Proof.
  destruct en; introv x; simpl; auto.
  unfold eq_utok_ren_en in x.
  f_equal.
  unfold app_utok_c.
  rw x; auto.
Qed.
*)

Lemma replace_opid_eq {p d} :
  forall o (r1 r2 : @utok_ren_o p d o),
    eq_utok_ren_o o r1 r2
    -> replace_opid o r1 = replace_opid o r2.
Proof.
  destruct o; introv x; allsimpl; auto.
  - apply eq_utok_ren_o_implies_c in x.
    apply eq_can.
    apply replace_can_eq; auto.
Qed.

Lemma utok_ren_2ot {p d} :
  forall o bts,
    @utok_ren_o p d o
    -> @utok_ren_bs p d bts
    -> @utok_ren p d (oterm o bts).
Proof.
  introv s1 s2.
  unfold utok_ren; intro k; exrepnd; allsimpl.
  unfold utok_ren_o in s1.
  unfold utok_ren_bs in s2.
  allrw @dset_member_iff.
  allrw in_app_iff; dorn k0.
  apply s1; exists x; rw @dset_member_iff; auto.
  apply s2; exists x; rw @dset_member_iff; auto.
Qed.

Lemma replace_utokens_t_eq {p d} :
  forall t (w1 w2 : wf_term t) (r1 r2 : @utok_ren p d t),
    eq_utok_ren t r1 r2
    -> replace_utokens_t t w1 r1 = replace_utokens_t t w2 r2.
Proof.
  nterm_ind t as [|f|o lbt ind] Case; simpl; introv e; auto.

  { f_equal.
    apply functional_extensionality; introv.
    f_equal; eauto with pi. }

  apply oterm_eq.
  apply eq_utok_ren_implies_o in e.

  - apply replace_opid_eq; auto.

  - apply eq_utok_ren_implies_bs in e.

    remember (utok_ren_2bs o lbt r1) as rs1.
    clear Heqrs1.
    remember (utok_ren_2bs o lbt r2) as rs2.
    clear Heqrs2.
    remember (wf_term_2bs o lbt w1) as ws1.
    clear Heqws1.
    remember (wf_term_2bs o lbt w2) as ws2.
    clear Heqws2.

    revert ws1 ws2 rs1 rs2 e.
    allapply @wf_term_2bs.

    induction lbt; auto.
    introv e.
    apply eq_cons.

    + destruct a; simpl.
      apply bterm_eq; auto.
      apply ind with (lv := l); simpl; auto.
      unfold eq_utok_ren, utok_ren_b_2t, utok_ren_bs_2b, utok_ren_2bs.
      introv; exrepnd.
      apply e.

    + apply IHlbt.
      * introv i k.
        apply ind with (lv := lv); simpl; sp.
      * allrw @wf_bterms_cons; sp.
      * allrw @wf_bterms_cons; sp.
      * apply utok_ren_2o in r1.
        apply utok_ren_2ot; auto.
        clear e.
        apply utok_ren_bs_2bs in rs1; auto.
      * apply utok_ren_2o in r1.
        apply utok_ren_2ot; auto.
        clear e.
        apply utok_ren_bs_2bs in rs1; auto.
      * apply eq_utok_ren_bs_cons_implies_bs; auto.
Qed.

Lemma replace_utokens_hyp_eq {p d} :
  forall h w1 w2 (r1 r2 : @utok_ren_hyp p d h),
    eq_utok_ren_hyp h r1 r2
    -> replace_utokens_hyp h w1 r1 = replace_utokens_hyp h w2 r2.
Proof.
  destruct h; simpl; introv e.
  unfold replace_utokens_hyp; simpl.
  apply equal_hyps.
  apply replace_utokens_t_eq; auto.
Qed.

Lemma replace_utokens_bhyps_eq {p d} :
  forall hs w1 w2 (r1 r2 : @utok_ren_bhyps p d hs),
    eq_utok_ren_bhyps hs r1 r2
    -> replace_utokens_bhyps hs w1 r1 = replace_utokens_bhyps hs w2 r2.
Proof.
  induction hs; simpl; introv e; auto.
  apply eq_cons.
  - apply replace_utokens_hyp_eq.
    introv; exrepnd.
    unfold utok_ren_bhyps_2h.
    apply e.
  - apply IHhs.
    unfold eq_utok_ren_bhyps in e.
    introv; exrepnd.
    unfold utok_ren_bhyps_2bhyps.
    apply e.
Qed.

Lemma replace_utokens_concl_eq {p d} :
  forall c w1 w2 (r1 r2 : @utok_ren_concl p d c),
    eq_utok_ren_concl c r1 r2
    -> replace_utokens_concl c w1 r1 = replace_utokens_concl c w2 r2.
Proof.
  introv e.
  destruct c; allsimpl.
  - apply eq_concl_ext; apply replace_utokens_t_eq; introv; exrepnd; simpl; auto.
  - apply eq_concl_typ; apply replace_utokens_t_eq; introv; exrepnd; simpl; auto.
Qed.

Lemma replace_utokens_bseq_eq {p d} :
  forall s w1 w2 (r1 r2 : @utok_ren_bseq p d s),
    eq_utok_ren_bseq s r1 r2
    -> replace_utokens_bseq s w1 r1 = replace_utokens_bseq s w2 r2.
Proof.
  introv e.
  destruct s.
  unfold replace_utokens_bseq.
  apply eq_baresequent; simpl.
  - apply replace_utokens_bhyps_eq.
    introv; exrepnd; simpl; auto.
  - apply replace_utokens_concl_eq.
    introv; exrepnd; simpl; auto.
Qed.

Lemma wf_hyps_snoc2h {o} :
  forall h (hs : @bhyps o), wf_hyps (snoc hs h) -> wf_term (htyp h).
Proof.
  introv wf; allrw @wf_hyps_snoc; tcsp.
Qed.

Lemma wf_hyps_snoc2hs {o} :
  forall h (hs : @bhyps o), wf_hyps (snoc hs h) -> wf_hyps hs.
Proof.
  introv wf; allrw @wf_hyps_snoc; tcsp.
Qed.

Lemma replace_utokens_bhyps_snoc {p d} :
  forall (h : hypothesis)
         (hs : list hypothesis)
         (w : wf_hyps (snoc hs h))
         (r : @utok_ren_bhyps p d (snoc hs h)),
    replace_utokens_bhyps (snoc hs h) w r
    = snoc (replace_utokens_bhyps hs (wf_hyps_snoc2hs h hs w) (utok_ren_bhyps_snoc_2bhyps h hs r))
           (replace_utokens_hyp h (wf_hyps_snoc2h h hs w) (utok_ren_bhyps_snoc_2h h hs r)).
Proof.
  induction hs; simpl; introv.

  - apply eq_cons; auto.
    apply replace_utokens_hyp_eq.
    introv; exrepnd; allsimpl.
    gen_in_utok; PI2.

  - apply eq_cons.

    + apply replace_utokens_hyp_eq.
      introv; exrepnd; allsimpl.
      gen_in_utok; PI2.

    + rw IHhs.
      apply eq_snoc.

      * apply replace_utokens_hyp_eq.
        introv; exrepnd; allsimpl.
        gen_in_utok; PI2.

      * apply replace_utokens_bhyps_eq.
        introv; exrepnd; allsimpl.
        gen_in_utok; PI2.
Qed.

Lemma wf_hyps_app_left {o} :
  forall (hs1 hs2 : @bhyps o), wf_hyps (hs1 ++ hs2) -> wf_hyps hs1.
Proof.
  introv wf; allrw @wf_hyps_app; sp.
Qed.

Lemma wf_hyps_app_right {o} :
  forall (hs1 hs2 : @bhyps o), wf_hyps (hs1 ++ hs2) -> wf_hyps hs2.
Proof.
  introv wf; allrw @wf_hyps_app; sp.
Qed.

Lemma replace_utokens_bhyps_app {p d} :
  forall (hs1 hs2 : list hypothesis)
         (w : wf_hyps (hs1 ++ hs2))
         (r : @utok_ren_bhyps p d (hs1 ++ hs2)),
    replace_utokens_bhyps (hs1 ++ hs2) w r
    = (replace_utokens_bhyps hs1 (wf_hyps_app_left hs1 hs2 w) (utok_ren_bhyps_app_2bhyps1 hs1 hs2 r))
        ++ (replace_utokens_bhyps hs2 (wf_hyps_app_right hs1 hs2 w) (utok_ren_bhyps_app_2bhyps2 hs1 hs2 r)).
Proof.
  induction hs1; simpl; introv.
  - apply replace_utokens_bhyps_eq.
    introv; exrepnd; simpl.
    gen_in_utok; PI2.

  - apply eq_cons.

    + apply replace_utokens_hyp_eq.
      introv; exrepnd; allsimpl.
      gen_in_utok; PI2.

    + rw IHhs1.
      apply app_if.

      * apply replace_utokens_bhyps_eq.
        introv; exrepnd; allsimpl.
        gen_in_utok; PI2.

      * apply replace_utokens_bhyps_eq.
        introv; exrepnd; allsimpl.
        gen_in_utok; PI2.
Qed.

Lemma vars_hyps_replace_utokens_bhyps {p d} :
  forall hs w (r : @utok_ren_bhyps p d hs),
    vars_hyps (replace_utokens_bhyps hs w r)
    = vars_hyps hs.
Proof.
  induction hs; introv; allsimpl; auto.
  apply eq_cons; auto.
Qed.

Lemma nh_vars_hyps_replace_utokens_bhyps {p d} :
  forall hs w (r : @utok_ren_bhyps p d hs),
    nh_vars_hyps (replace_utokens_bhyps hs w r)
    = nh_vars_hyps hs.
Proof.
  induction hs; introv; allsimpl; auto.
  allunfold @nh_vars_hyps; simpl.
  destruct a; allsimpl.
  allunfold @replace_utokens_hyp; allsimpl.
  allunfold @is_nh; allsimpl.
  destruct hidden; allsimpl; auto.
  apply eq_cons; auto.
Qed.

Lemma op_bindings_replace_opid {p d} :
  forall o (r : @utok_ren_o p d o),
    OpBindings (replace_opid o r)
    = OpBindings o.
Proof.
  destruct o; introv; allsimpl; auto.
  - destruct c; auto.
Qed.

Lemma free_vars_replace_utokens {p d} :
  forall t w (r : @utok_ren p d t),
    free_vars (replace_utokens_t t w r) = free_vars t.
Proof.
  nterm_ind t as [|f|o lbt ind] Case; simpl; auto; introv.

  remember (utok_ren_2bs o lbt r) as rs.
  clear Heqrs r.
  remember (wf_term_2bs o lbt w) as ws.
  clear Heqws.

  allapply @wf_term_2bs.

  induction lbt; allsimpl; auto.
  apply app_if.

  - destruct a; allsimpl.
    rw (ind n l); auto.

  - apply IHlbt.

    + introv k; introv.
      apply (ind nt lv); sp.

    + allrw @wf_bterms_cons; sp.
Qed.

Lemma so_free_vars_replace_utokens_so {p d} :
  forall (t : @SOTerm p) (w : wf_soterm t) (r : @utok_ren_so p d t),
    so_free_vars (replace_utokens_so t w r) = so_free_vars t.
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv; allsimpl; auto.

  - Case "sovar".
    f_equal; tcsp.

    + f_equal.
      remember (utok_ren_so_2ts v ts r) as rs.
      remember (wf_sovar_2ts v ts w) as ws.
      clear Heqrs Heqws r ind.
      induction ts; simpl; tcsp.
      rewrite IHts; auto.
      apply wf_sovar; introv i.
      apply wf_soterms_2ts in ws.
      apply ws; auto.

    + remember (utok_ren_so_2ts v ts r) as rs.
      remember (wf_sovar_2ts v ts w) as ws.
      clear Heqrs Heqws r.
      induction ts; simpl; tcsp.
      rw ind; tcsp.
      apply app_if; auto.
      apply IHts.
      { introv i; introv.
        apply ind; tcsp. }
      { apply wf_sovar; introv i.
        apply wf_soterms_2ts in ws.
        apply ws; auto. }

  - Case "soterm".
    remember (utok_ren_so_2bs op bs r) as r'.
    remember (wf_soterm_2bs op bs w) as w'.
    clear Heqr' Heqw' r.

    apply wf_soterm_iff in w; repnd.
    clear w0.

    induction bs; simpl; auto.
    destruct a as [l t]; simpl.
    rw (ind t l); tcsp.
    apply app_if; auto.
    apply IHbs.
    { introv i; introv.
      apply (ind t0 vs); tcsp. }
    { introv i.
      eapply w; simpl; eauto. }
Qed.

Lemma free_vars_set_patom_noutokens {p d} :
  forall t w nu, free_vars (@set_patom_noutokens p d t w nu) = free_vars t.
Proof.
  nterm_ind t as [|f|o lbt ind] Case; simpl; auto; introv.

  remember (noutokens_2bs o lbt w) as nus.
  clear Heqnus.
  remember (wf_term_2bs o lbt nu) as ws.
  clear Heqws.

  clear w nu.

  induction lbt; allsimpl; auto.
  apply app_if.

  - destruct a; allsimpl.
    rw (ind n l); auto.

  - apply IHlbt.
    introv k; introv.
    apply (ind nt lv); sp.
Qed.

Lemma get_utokens_set_patom_noutokens {p d} :
  forall t wf nu, get_utokens (@set_patom_noutokens p d t wf nu) = [].
Proof.
  nterm_ind t as [|f ind|o lbt ind] Case; simpl; auto; introv.

  apply app_eq_nil_iff; dands.

  { destruct o; simpl; auto.
    destruct c; allsimpl; auto.
    unfold noutokens in wf; allsimpl; ginv. }

  remember (noutokens_2bs o lbt wf) as nus.
  clear Heqnus.
  remember (wf_term_2bs o lbt nu) as ws.
  clear Heqws.

  clear wf nu.

  induction lbt; allsimpl; auto.
  apply app_eq_nil_iff; dands.

  - destruct a; allsimpl.
    rw (ind n l); auto.

  - apply IHlbt.
    introv k; introv.
    apply (ind nt lv); sp.
Qed.

Lemma op_bindings_set_patom_noutokens_o {p d} :
  forall o nu,
    OpBindings (@set_patom_noutokens_o p d o nu)
    = OpBindings o.
Proof.
  destruct o; introv; allsimpl; auto.
  destruct c; simpl; auto.
  unfold noutokens_o in nu; allsimpl; ginv.
Qed.

Lemma nt_wf_set_patom_noutokens {p d} :
  forall t wf nu, nt_wf (@set_patom_noutokens p d t nu wf).
Proof.
  nterm_ind t as [|f ind|o lbt ind] Case; simpl; auto.

  { introv nu.
    dup wf as nwf; rw @wf_term_eq in nwf.
    allrw @nt_wf_sterm_iff; introv.
    pose proof (nwf n) as q; clear nwf; repnd.
    unfold closed; rw @free_vars_set_patom_noutokens; rw q1.
    unfold noutokens; rw @get_utokens_set_patom_noutokens.
    dands; auto. }

  introv.

  remember (noutokens_2bs o lbt nu) as nus.
  clear Heqnus.
  remember (wf_term_2bs o lbt wf) as wfs.
  clear Heqwfs.

  rw @wf_term_eq in wf.
  allrw @nt_wf_oterm_iff; repnd; dands.

  - rw @op_bindings_set_patom_noutokens_o.
    rw <- wf0.
    clear nu wf0 wf ind.
    induction lbt; simpl; auto.
    apply eq_cons; auto.
    destruct a; simpl; auto.

  - introv k.
    destruct b.
    constructor.
    clear wf0 nu.
    induction lbt; allsimpl; auto; tcsp.
    repndors.

    + destruct a; allsimpl.
      clear IHlbt.
      inversion k; subst; GC.
      apply ind with (lv := l); auto.

    + apply IHlbt in k; auto; clear IHlbt.
      introv j; introv.
      apply ind with (lv := lv); sp.
Qed.

Lemma nt_wf_replace_utokens {p d} :
  forall t w (r : @utok_ren p d t), nt_wf (replace_utokens_t t w r).
Proof.
  nterm_ind t as [|f ind|o lbt ind] Case; simpl; auto.

  { introv s.
    dup w as wf; rw @wf_term_eq in wf.
    allrw @nt_wf_sterm_iff; introv.
    pose proof (wf n) as q; clear wf; repnd.
    unfold closed; rw @free_vars_set_patom_noutokens; rw q1.
    unfold noutokens; rw @get_utokens_set_patom_noutokens.
    dands; auto.
    apply nt_wf_set_patom_noutokens. }

  introv.

  remember (utok_ren_2bs o lbt r) as rs.
  clear Heqrs.
  remember (wf_term_2bs o lbt w) as ws.
  clear Heqws.

  rw @wf_term_eq in w.
  allrw @nt_wf_oterm_iff; repnd; dands.

  - rw @op_bindings_replace_opid.
    rw <- w0.
    clear w0 r w ind.
    induction lbt; simpl; auto.
    apply eq_cons; auto.
    destruct a; simpl; auto.

  - introv k.
    destruct b.
    constructor.
    clear w0.
    induction lbt; allsimpl; auto; tcsp.
    dorn k.
    + destruct a; allsimpl.
      clear IHlbt.
      inversion k; subst; GC.
      apply ind with (lv := l); auto.

    + apply IHlbt in k; auto.

      { introv kk; introv.
        apply ind with (lv := lv); sp. }

      { apply utok_ren_2ot; auto.
        apply utok_ren_2o in r; auto.
        clear k.
        apply utok_ren_bs_2bs in rs; auto. }
Qed.

Lemma wf_term_replace_utokens {p d} :
  forall (t : @NTerm p) w (r : @utok_ren p d t),
    wf_term (replace_utokens_t t w r).
Proof.
  introv.
  allrw @wf_term_eq.
  apply nt_wf_replace_utokens; auto.
Qed.

Lemma utok_ren_sovar_tl {p d} :
  forall v (t : @SOTerm p) ts,
    @utok_ren_so p d (sovar v (t :: ts))
    -> @utok_ren_so p d (sovar v ts).
Proof.
  introv r.
  introv h; exrepnd.
  apply r.
  exists x; allsimpl.
  allrw @dset_member_iff.
  allrw in_app_iff; sp.
Defined.

Lemma utok_ren_soterm_tl {p d} :
  forall op (b : @SOBTerm p) bs,
    @utok_ren_so p d (soterm op (b :: bs))
    -> @utok_ren_so p d (soterm op bs).
Proof.
  introv r.
  introv h; exrepnd.
  apply r.
  exists x; allsimpl.
  allrw @dset_member_iff.
  allrw in_app_iff; sp.
Defined.

(* !! MOVE *)
Lemma wf_term_oterm {o} :
  forall op (bs : list (@BTerm o)),
    wf_term (oterm op bs)
    <=> (map num_bvars bs = OpBindings op
         # (forall b : BTerm, LIn b bs -> wf_bterm b)).
Proof.
  introv.
  rw @wf_term_eq.
  rw @nt_wf_oterm_iff.
  split; introv k; repnd; dands; auto;
  introv i; apply bt_wf_eq; auto.
Qed.

Lemma wf_term_replace_utokens_so {p d} :
  forall (t : @SOTerm p) (w : wf_soterm t) (r : @utok_ren_so p d t),
    wf_soterm (replace_utokens_so t w r).
Proof.
  unfold wf_soterm.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv; allsimpl; auto.

  - Case "sovar".
    remember (utok_ren_so_2ts v ts r) as r'.
    remember (wf_sovar_2ts v ts w) as w'.
    clear Heqr' Heqw'.

    allrw @wf_apply_solist; repnd; dands; auto.

    induction ts; simpl; introv i; tcsp.
    repndors; subst; auto.

    + apply ind; tcsp.

    + apply IHts in i; auto.
      * introv k; apply ind; sp.
      * apply utok_ren_sovar_tl in r; auto.
      * introv k; apply w; sp.

  - Case "soseq".
    apply wf_sterm_iff.
    dup w as w'; rw @wf_sterm_iff in w'.
    introv.
    pose proof (w' n) as h.
    allrw @isprog_nout_iff.
    unfold set_patom_noutokens_ntseq; simpl.
    repnd; dands.

    + apply nt_wf_set_patom_noutokens.

    + unfold closed.
      rewrite free_vars_set_patom_noutokens; auto.

    + unfold noutokens.
      rewrite get_utokens_set_patom_noutokens; auto.

  - Case "soterm".
    remember (utok_ren_so_2bs op bs r) as r'; clear Heqr'.
    remember (wf_soterm_2bs op bs w) as w'; clear Heqw'.
    allrw @wf_term_oterm; repnd.
    allrw map_map.
    dands.

    + rw @op_bindings_replace_opid.
      rw <- w0.
      clear w w0 r ind.
      induction bs; simpl; auto.
      f_equal; auto.
      unfold compose.
      destruct a; unfold num_bvars; simpl; auto.

    + introv i.
      rw in_map_iff in i; exrepnd; subst.
      destruct a as [l t]; allsimpl.
      apply bt_wf_eq.
      constructor.
      apply nt_wf_eq.
      clear w0 r.
      induction bs; allsimpl; tcsp.
      dorn i1.

      * destruct a as [l' t']; allsimpl.
        inversion i1; subst l t; clear i1.
        eapply ind; eauto.

      * eapply IHbs; eauto.
Qed.

Lemma isprog_vars_replace_utokens_t {p d} :
  forall hs w1 (r1 : @utok_ren_bhyps p d hs) t w2 (r2 : @utok_ren p d t),
    isprog_vars (vars_hyps hs) t
    -> isprog_vars
         (vars_hyps (replace_utokens_bhyps hs w1 r1))
         (replace_utokens_t t w2 r2).
Proof.
  introv.
  rw @vars_hyps_replace_utokens_bhyps.
  allrw @isprog_vars_eq.
  introv k; repnd.
  rw @free_vars_replace_utokens; dands; auto.
  apply nt_wf_replace_utokens; auto.
Qed.

Lemma wf_hypotheses_replace_aux {p d} :
  forall (hyps : barehypotheses)
         (r : @utok_ren_bhyps p d hyps)
         (w : wf_hypotheses hyps)
         (wf : wf_hyps hyps),
    wf_hypotheses (replace_utokens_bhyps hyps wf r).
Proof.
  introv w; introv.
  induction hyps using rev_list_indT; allsimpl; auto.
  rw @wf_hypotheses_snoc in w; repnd.
  rw @replace_utokens_bhyps_snoc.
  apply hyps_cons; auto.
  - destruct a; allsimpl.
    apply isprog_vars_replace_utokens_t; auto.
  - destruct a; allsimpl.
    rw @vars_hyps_replace_utokens_bhyps; auto.
Qed.

Lemma wf_hypotheses_replace {p d} :
  forall (hyps : barehypotheses)
         (r : @utok_ren_bhyps p d hyps)
         (w : wf_hypotheses hyps),
    wf_hypotheses (replace_utokens_bhyps hyps (wf_hypotheses_implies_wf_hyps hyps w) r).
Proof.
  introv.
  apply wf_hypotheses_replace_aux; auto.
Qed.

Lemma wf_concl_replace {p d} :
  forall (c : conclusion) (r : @utok_ren_concl p d c) (w : wf_concl c),
    wf_concl (replace_utokens_concl c w r).
Proof.
  introv.
  destruct c; allsimpl; constructor; simpl; auto;
  inversion w as [wt we]; allsimpl; auto;
  apply wf_term_replace_utokens; auto.
Qed.

Lemma wf_sequent_replace {p d} :
  forall (s : baresequent) (r : @utok_ren_bseq p d s) (w : wf_sequent s),
    wf_sequent (replace_utokens_bseq s w r).
Proof.
  introv.
  unfold wf_sequent.
  unfold wf_sequent in w; repnd.
  destruct s; allsimpl; repnd; dands.

  - allrw @vswf_hypotheses_nil_eq.
    apply wf_hypotheses_replace_aux; auto.

  - apply wf_concl_replace; auto.
Qed.

Definition replace_utokens_seq {p d}
           (s : @sequent p) :
  @utok_ren_seq p d s -> @sequent (set_patom p d) :=
  match s with
    | existT _ bs w =>
      fun r =>
        existT
          wf_sequent
          (replace_utokens_bseq bs w (utok_ren_seq_2bseq bs w r))
          (wf_sequent_replace bs (utok_ren_seq_2bseq bs w r) w)
  end.

Definition utok_ren_ctseq_2seq {p d}
           (s : sequent)
           (q : closed_type_sequent s)
           (r : @utok_ren_ctseq p d (existT _ s q)) : utok_ren_seq s := r.

Lemma closed_type_sequent_replace {p d} :
  forall (s : sequent) (r : @utok_ren_seq p d s),
    closed_type_sequent s
    -> closed_type_sequent (replace_utokens_seq s r).
Proof.
  introv c.
  allunfold @closed_type_sequent.
  allunfold @closed_type_baresequent.
  allunfold @closed_type.
  allunfold @covered.
  destruct s; allsimpl.
  destruct x; allsimpl.
  destruct concl; allsimpl;
  rw @free_vars_replace_utokens;
  rw @vars_hyps_replace_utokens_bhyps; auto.
Qed.

Definition replace_utokens_ctseq {p d}
           (cts : @ctsequent p) :
  @utok_ren_ctseq p d cts -> @ctsequent (set_patom p d) :=
  match cts with
    | existT _ s q =>
      fun r =>
        existT
          closed_type_sequent
          (replace_utokens_seq s (utok_ren_ctseq_2seq s q r))
          (closed_type_sequent_replace s (utok_ren_ctseq_2seq s q r) q)
  end.

Lemma closed_extract_ctsequent_replace {p d} :
  forall (s : ctsequent) (r : @utok_ren_ctseq p d s),
    closed_extract_ctsequent s
    -> closed_extract_ctsequent (replace_utokens_ctseq s r).
Proof.
  introv c.
  allunfold @closed_extract_ctsequent.
  allunfold @closed_extract_sequent.
  allunfold @closed_extract_baresequent.
  allunfold @closed_extract.
  allunfold @covered_op.
  allunfold @covered.
  destruct s; allsimpl.
  destruct x; allsimpl.
  destruct x; allsimpl.
  destruct concl; allsimpl;
  allrw @free_vars_replace_utokens;
  allrw @vars_hyps_replace_utokens_bhyps;
  allrw @nh_vars_hyps_replace_utokens_bhyps;
  auto.
Qed.

Definition utok_ren_cseq_2ctseq {p d}
           (s : ctsequent)
           (q : closed_extract_ctsequent s)
           (r : @utok_ren_cseq p d (existT _ s q)) : utok_ren_ctseq s := r.

Definition utok_ren_lib_entry_2rhs {p d}
           (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : SOTerm)
           (correct : correct_abs opabs vars rhs)
           (r : @utok_ren_library_entry p d (lib_abs opabs vars rhs correct))
: utok_ren_so rhs := r.

Definition replace_utokens_cseq {p d}
           (cs : @csequent p) :
  @utok_ren_cseq p d cs -> @csequent (set_patom p d) :=
  match cs with
    | existT _ s q =>
      fun r =>
        existT
          closed_extract_ctsequent
          (replace_utokens_ctseq s (utok_ren_cseq_2ctseq s q r))
          (closed_extract_ctsequent_replace s (utok_ren_cseq_2ctseq s q r) q)
  end.

Lemma subvars_eq_l :
  forall vs1 vs2 vs,
    vs2 = vs1 -> subvars vs1 vs -> subvars vs2 vs.
Proof. sp; subst; sp. Qed.

Lemma subsovars_eq_l :
  forall vs1 vs2 vs,
    vs2 = vs1 -> subsovars vs1 vs -> subsovars vs2 vs.
Proof. sp; subst; sp. Qed.

(* !!MOVE to list *)
Lemma in_app_if_fst :
  forall A (l1 l2 : list A) a,
    LIn a l1 -> LIn a (l1 ++ l2).
Proof.
  induction l1; introv i; allsimpl; tcsp.
Defined.

(* !!MOVE to list *)
Lemma in_app_if_snd :
  forall A (l1 l2 : list A) a,
    LIn a l2 -> LIn a (l1 ++ l2).
Proof.
  induction l1; introv i; allsimpl; tcsp.
Defined.

(* !!MOVE to list *)
Definition fmapin_app_fst {A B l1 l2}
           (f : forall a : A, LIn a (l1 ++ l2) -> B)
: forall a : A, LIn a l1 -> B :=
  fun a i => f a (in_app_if_fst A l1 l2 a i).

(* !!MOVE to list *)
Definition fmapin_app_snd {A B l1 l2}
           (f : forall a : A, LIn a (l1 ++ l2) -> B)
: forall a : A, LIn a l2 -> B :=
  fun a i => f a (in_app_if_snd A l1 l2 a i).

(* !!MOVE to list *)
Lemma mapin_app :
  forall A B (l1 l2 : list A) (f : forall a : A, LIn a (l1 ++ l2) -> B),
    mapin (l1 ++ l2) f
    = mapin l1 (fmapin_app_fst f) ++ mapin l2 (fmapin_app_snd f).
Proof.
  induction l1; introv; allsimpl; auto.
  f_equal.
  rw IHl1.
  apply app_if; auto.
Qed.

Lemma in_utok_so_ts_if_mem {o} :
  forall (u : get_patom_set o) (t : SOTerm) (ts : list SOTerm),
    LIn t ts
    -> dset_member u (get_utokens_so t)
    -> dset_member u (flat_map get_utokens_so ts).
Proof.
  introv i d.
  allrw @dset_member_iff.
  rw lin_flat_map.
  exists t; auto.
Qed.

Definition utok_ren_ts_agree {o d}
           (ts : list SOTerm)
           (t : SOTerm)
           (u : @utok_ren_so_ts o d ts)
           (r : @utok_ren_so o d t) :=
  forall (a : get_patom_set o)
         (i : dset_member a (get_utokens_so_ts ts)),
    {j : dset_member a (get_utokens_so t)
     & u (existT _ a i) = r (existT _ a j)}.

Definition utok_ren_bs_agree {o d}
           (bs : list SOBTerm)
           (t : SOTerm)
           (u : @utok_ren_so_bs o d bs)
           (r : @utok_ren_so o d t) :=
  forall (a : get_patom_set o)
         (i : dset_member a (get_utokens_so_bs bs)),
    {j : dset_member a (get_utokens_so t)
     & u (existT _ a i) = r (existT _ a j)}.

Lemma get_utokens_so_replace_utokens_so {o d} :
  forall (t : @SOTerm o) (w : wf_soterm t) (r : @utok_ren_so o d t),
    get_utokens_so (replace_utokens_so t w r)
    = mapin (get_utokens_so t)
            (fun (a : get_patom_set o)
                 (i : LIn a (get_utokens_so t)) =>
               r (existT _ a (dset_member_if a (get_utokens_so t) i))).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv; allsimpl; auto.

  - Case "sovar".
    remember (utok_ren_so_2ts v ts r) as u.
    remember (wf_sovar_2ts v ts w) as wf.

    assert (utok_ren_ts_agree ts (sovar v ts) u r) as agree.
    { subst; introv; exists (in_utok_so_if_ts _ v _ i); auto. }

    clear Hequ.
    clear Heqwf.
    allrw @wf_sovar.

    induction ts; simpl; tcsp.
    rw mapin_app; apply app_if; simpl.

    + unfold fmapin_app_fst.
      pose proof (ind a) as h1; simpl in h1; autodimp h1 hyp; clear ind.
      pose proof (h1 (wf_soterms_2t a ts wf) (utok_ren_so_ts_2t a ts u)) as h2; clear h1.
      rw h2.
      apply eq_mapins.
      introv; simpl.
      pose proof (agree a0 (in_utok_so_ts_if_t a0 a ts (dset_member_if a0 (get_utokens_so a) i))) as ag.
      exrepnd; allsimpl.
      rewrite ag0; clear ag0.
      f_equal; f_equal.
      apply dset_member_proof_irrelevance.

    + repeat (autodimp IHts hyp).
      {
        introv i; introv.
        pose proof (ind t) as h; simpl in h; autodimp h hyp.
      }

      pose proof (IHts
                    (utok_ren_sovar_tl _ _ _ r)
                    (utok_ren_so_ts_2ts a ts u)
                    (wf_soterms_2ts a ts wf)) as h; clear IHts.
      repeat (autodimp h hyp).
      {
        introv.
        pose proof (agree a0 (in_utok_so_ts_if_ts _ _ _ i)) as k; exrepnd.
        exists (in_utok_so_if_ts _ v _ i); allsimpl.
        rw k0.
        f_equal; f_equal.
        apply dset_member_proof_irrelevance.
      }

      { allsimpl; introv i; apply w; simpl; auto. }

      rw h; clear h.
      apply eq_mapins.
      introv; simpl.
      unfold fmapin_app_snd.
      f_equal; f_equal.
      apply dset_member_proof_irrelevance.

  - Case "soterm".
    rw mapin_app.
    f_equal.

    + destruct op; simpl; tcsp.

      * destruct c; simpl; auto.
        unfold app_utok_c, utok_ren_o2c, fmapin_app_fst.
        unfold utok_ren_so_2o.
        f_equal; f_equal; f_equal.
        apply dset_member_proof_irrelevance.

    + remember (utok_ren_so_2bs op bs r) as u.
      remember (wf_soterm_2bs op bs w) as wf.

      assert (utok_ren_bs_agree bs (soterm op bs) u r) as agree.
      { subst; introv; exists (in_utok_so_if_bts _ op _ i); auto. }

      clear Hequ.
      clear Heqwf.
      allrw @wf_soterm_iff; repnd.
      clear w0.

      induction bs; simpl; auto.
      rw mapin_app; apply app_if; simpl.

      * clear IHbs.
        destruct a as [l t]; simpl.
        unfold fmapin_app_fst.
        rw (ind t l); simpl; auto.
        apply eq_mapins.
        introv; simpl.
        unfold fmapin_app_snd; simpl.
        pose proof (agree a (in_utok_so_bs_if_b a (sobterm l t) bs (in_utok_so_b_if_t a l t (dset_member_if a (get_utokens_so t) i)))) as ag.
        exrepnd; allsimpl.
        rewrite ag0; clear ag0.
        f_equal; f_equal.
        apply dset_member_proof_irrelevance.

      * repeat (autodimp IHbs hyp).
        {
          introv i; introv.
          apply (ind t vs); simpl; auto.
        }

        pose proof (IHbs
                      (utok_ren_soterm_tl _ _ _ r)
                      (utok_ren_so_bs_2bs a bs u)
                      (wf_sobterms_2bs a bs wf)) as h; clear IHbs.
        repeat (autodimp h hyp).
        {
          introv.
          pose proof (agree a0 (in_utok_so_bs_if_bs _ _ _ i)) as k; exrepnd.
          exists (in_utok_so_if_bts _ op _ i); allsimpl.
          rw k0.
          f_equal; f_equal.
          apply dset_member_proof_irrelevance.
        }

        { introv i.
          pose proof (w vs t) as xx; simpl in xx; autodimp xx hyp. }

        rw h; clear h.
        apply eq_mapins.
        introv; simpl.
        unfold fmapin_app_snd.
        f_equal; f_equal.
        apply dset_member_proof_irrelevance.
Qed.

Lemma no_utokens_replace_utokens_so {p d} :
  forall (t : @SOTerm p) (w : wf_soterm t) (r : @utok_ren_so p d t),
    no_utokens t -> no_utokens (replace_utokens_so t w r).
Proof.
  introv nu.
  allunfold @no_utokens.
  rw @get_utokens_so_replace_utokens_so.
  apply null_iff_nil.
  introv i.
  apply in_mapin in i; exrepnd; subst.
  rw nu in i; simpl in i; sp.
Qed.

Definition replace_utokens_correct_abs {p d}
           (opabs : opabs)
           (vars : list sovar_sig)
           (rhs : @SOTerm p)
           (correct : correct_abs opabs vars rhs)
           (r : @utok_ren_so p d rhs) :
  correct_abs opabs vars (replace_utokens_so rhs (fst correct) r) :=
  match correct with
    | (w,(sv,(cap,(ms,nu)))) =>
      (wf_term_replace_utokens_so rhs w r,
       (subsovars_eq_l (so_free_vars rhs)
                       (so_free_vars (replace_utokens_so rhs w r))
                       vars
                       (so_free_vars_replace_utokens_so rhs w r)
                       sv,
        (cap, (ms, no_utokens_replace_utokens_so rhs w r nu))))
  end.

Definition replace_utokens_library_entry {p d}
           (entry : @library_entry p) :
  @utok_ren_library_entry p d entry -> @library_entry (set_patom p d) :=
  match entry with
    | lib_abs opabs vars rhs correct =>
      fun r =>
        lib_abs
          opabs
          vars
          (replace_utokens_so rhs (fst correct) (utok_ren_lib_entry_2rhs opabs vars rhs correct r))
          (replace_utokens_correct_abs opabs vars rhs correct r)
  end.

Fixpoint replace_utokens_library {p d}
           (lib : @library p) :
  @utok_ren_library p d lib -> @library (set_patom p d) :=
  match lib with
    | [] => fun _ => []
    | e :: es =>
      fun r =>
        (replace_utokens_library_entry e (utok_ren_lib_2e e es r))
          :: (replace_utokens_library es (utok_ren_lib_2es e es r))
  end.

End TokenReplacing.



Definition sequent_atom_true {p} lib (S : @csequent (set_dset_string p)) : Type :=
  forall k : nat,
  forall D : Set,
  forall deq : Deq D,
  forall fresh : FreshFun D,
    has_at_least_k_elements k D
    -> forall f : @utok_ren_cseq (set_dset_string p) (mk_dset D deq fresh) S,
       forall fl : @utok_ren_library (set_dset_string p) (mk_dset D deq fresh) lib,
         VR_sequent_true (@replace_utokens_library
                            (set_dset_string p)
                            (mk_dset D deq fresh)
                            lib
                            fl)
                         (@replace_utokens_cseq
                            (set_dset_string p)
                            (mk_dset D deq fresh)
                            S
                            f).

Notation s2s := set_dset_string.

Definition rule_atom_true {o} lib (R : @rule (s2s o)) : Type :=
  forall wg : wf_sequent (goal R),
  forall cg : closed_type_baresequent (goal R),
  forall cargs: args_constraints (sargs R) (hyps (goal R)),
  forall hyps : (forall s : baresequent,
                   LIn s (subgoals R)
                   -> {c : wf_csequent s & sequent_atom_true lib (mk_wcseq s c)}),
    {c : closed_extract_baresequent (goal R)
     & sequent_atom_true lib (mk_wcseq (goal R) (ext_wf_cseq (goal R) wg cg c))}.

Definition sequent_atom_true2 {o} lib (s : @baresequent (set_dset_string o)) :=
  {c : wf_csequent s & sequent_atom_true lib (mk_wcseq s c)}.

Definition rule_atom_true2 {o} lib (R : @rule (set_dset_string o)) : Type :=
  forall pwf   : pwf_sequent (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> sequent_atom_true2 lib s),
    sequent_atom_true2 lib (goal R).

Ltac wf_gen :=
  let h := fresh "h" in
  match goal with
    | [ |- context[wf_sequent_replace ?s ?r ?w]               ] => remember (wf_sequent_replace s r w)               as h; clear_eq_l h
    | [ |- context[closed_type_sequent_replace ?s ?r ?c]      ] => remember (closed_type_sequent_replace s r c)      as h; clear_eq_l h
    | [ |- context[closed_extract_ctsequent_replace ?s ?r ?c] ] => remember (closed_extract_ctsequent_replace s r c) as h; clear_eq_l h

    | [ H : context[wf_sequent_replace ?s ?r ?w]               |- _ ] => remember (wf_sequent_replace s r w)               as h; clear_eq_l h
    | [ H : context[closed_type_sequent_replace ?s ?r ?c]      |- _ ] => remember (closed_type_sequent_replace s r c)      as h; clear_eq_l h
    | [ H : context[closed_extract_ctsequent_replace ?s ?r ?c] |- _ ] => remember (closed_extract_ctsequent_replace s r c) as h; clear_eq_l h
  end.

Ltac wf_gens := repeat wf_gen.

Lemma replace_utokens_cseq_mk_wcseq {p d} :
  forall (s : baresequent)
         (w : wf_csequent s)
         (f : @utok_ren_cseq p d (mk_wcseq s w)),
    {w' : wf_csequent (replace_utokens_bseq s (fst w) f)
     & replace_utokens_cseq (mk_wcseq s w) f
       = mk_wcseq (replace_utokens_bseq s (fst w) f) w'}.
Proof.
  introv.
  destruct s; allsimpl.
  allunfold @wf_csequent; allsimpl; repnd.
  allunfold @wf_sequent; allsimpl; repnd.
  unfold mk_wcseq in f; allsimpl.

  assert (wf_hypotheses
            (replace_utokens_bhyps
               hyps (wf_sequent_2hyps {| hyps := hyps; concl := concl |} (w2, w0))
               (utok_ren_bseq_2h {| hyps := hyps; concl := concl |} f))) as wfh.
  { apply wf_hypotheses_replace_aux; auto. }

  assert (wf_concl
            (replace_utokens_concl
               concl (wf_sequent_2concl {| hyps := hyps; concl := concl |} (w2, w0))
               (utok_ren_bseq_2c {| hyps := hyps; concl := concl |} f))) as wfc.
  { apply wf_concl_replace; auto. }

  assert (closed_type
            (replace_utokens_bhyps
               hyps (wf_sequent_2hyps {| hyps := hyps; concl := concl |} (w2, w0))
               (utok_ren_bseq_2h {| hyps := hyps; concl := concl |} f))
            (replace_utokens_concl
               concl (wf_sequent_2concl {| hyps := hyps; concl := concl |} (w2, w0))
               (utok_ren_bseq_2c {| hyps := hyps; concl := concl |} f))) as ct.
  { allunfold @closed_type.
    allunfold @covered; allsimpl.
    destruct concl; allsimpl;
    rw @free_vars_replace_utokens;
    rw @vars_hyps_replace_utokens_bhyps; auto. }

  assert (closed_extract
            (replace_utokens_bhyps
               hyps (wf_sequent_2hyps {| hyps := hyps; concl := concl |} (w2, w0))
               (utok_ren_bseq_2h {| hyps := hyps; concl := concl |} f))
            (replace_utokens_concl
               concl (wf_sequent_2concl {| hyps := hyps; concl := concl |} (w2, w0))
               (utok_ren_bseq_2c {| hyps := hyps; concl := concl |} f))) as ce.
  { allunfold @closed_extract.
    allunfold @covered_op.
    allunfold @covered.
    destruct concl; allsimpl;
    allrw @free_vars_replace_utokens;
    allrw @vars_hyps_replace_utokens_bhyps;
    allrw @nh_vars_hyps_replace_utokens_bhyps;
    auto. }

  apply vswf_hypotheses_nil_eq in wfh.

  exists ((wfh,wfc),(ct,ce)); simpl.

  apply eq_csequent; simpl.
  apply eq_ctsequent; simpl.
  apply eq_sequent; simpl.

  unfold replace_utokens_bseq; simpl.
  unfold mk_baresequent.

  apply eq_baresequent; simpl.

  - apply replace_utokens_bhyps_eq.
    intro; exrepnd; simpl; reflexivity.

  - apply replace_utokens_concl_eq.
    introv; exrepnd; simpl.
    reflexivity.
Qed.

Lemma rule_atom_true_iff_rule_atom_true2 {o} :
  forall lib (R : @rule (set_dset_string o)),
    rule_atom_true lib R <=> rule_atom_true2 lib R.
Proof.
  introv; split; unfold rule_true, rule_true2; intro rt.

  - introv pwf args hs.
    destruct pwf as [wg cg].
    generalize (rt wg cg args); clear rt; intro rt.
    dest_imp rt hyp.
    exrepnd.
    unfold sequent_true2.
    exists (wg,(cg,c)); sp.

  - introv args hs.
    generalize (rt (wg,cg) args); clear rt; intro rt.
    dest_imp rt hyp.
    unfold sequent_atom_true2 in rt; exrepnd.
    destruct c; repnd.
    exists p; sp.
    pose proof (wf_csequent_proof_irrelevance
                  (goal R)
                  (ext_wf_cseq (goal R) wg cg p)
                  (w, (p0, p))) as h; rw h; auto.
Qed.

Lemma utok_ren_cseq_id {o d} :
  forall s, @utok_ren_cseq (set_patom o d) d s.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_ctseq_id {o d} :
  forall s, @utok_ren_ctseq (set_patom o d) d s.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_seq_id {o d} :
  forall s, @utok_ren_seq (set_patom o d) d s.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_bseq_id {o d} :
  forall s, @utok_ren_bseq (set_patom o d) d s.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_bhyps_id {o d} :
  forall hs, @utok_ren_bhyps (set_patom o d) d hs.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_hyp_id {o d} :
  forall hs, @utok_ren_hyp (set_patom o d) d hs.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_concl_id {o d} :
  forall hs, @utok_ren_concl (set_patom o d) d hs.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_t_id {o d} :
  forall t, @utok_ren (set_patom o d) d t.
Proof.
  introv p; exrepnd; exact x.
Defined.

Lemma utok_ren_cseq_id_2ctseq {o d} :
  forall (s : ctsequent) (c : closed_extract_ctsequent s),
    utok_ren_cseq_2ctseq s c (@utok_ren_cseq_id o d (existT _ s c))
    = utok_ren_ctseq_id s.
Proof. sp. Qed.

Lemma utok_ren_ctseq_id_2seq {o d} :
  forall (s : sequent) (c : closed_type_sequent s),
    utok_ren_ctseq_2seq s c (@utok_ren_ctseq_id o d (existT _ s c))
    = utok_ren_seq_id s.
Proof. sp. Qed.

Lemma utok_ren_seq_id_2bseq {o d} :
  forall (s : baresequent) (c : wf_sequent s),
    utok_ren_seq_2bseq s c (@utok_ren_seq_id o d (existT _ s c))
    = utok_ren_bseq_id s.
Proof. sp. Qed.

Lemma utok_ren_bseq_id_2h {o d} :
  forall s,
    eq_utok_ren_bhyps
      (hyps s)
      (utok_ren_bseq_2h s (@utok_ren_bseq_id o d s))
      (utok_ren_bhyps_id (hyps s)).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma utok_ren_bseq_id_2c {o d} :
  forall s,
    eq_utok_ren_concl
      (concl s)
      (utok_ren_bseq_2c s (@utok_ren_bseq_id o d s))
      (utok_ren_concl_id (concl s)).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma utok_ren_bhyps_id_2h {o d} :
  forall h hs,
    eq_utok_ren_hyp
      h
      (utok_ren_bhyps_2h h hs (@utok_ren_bhyps_id o d (h :: hs)))
      (utok_ren_hyp_id h).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma utok_ren_hyp_id_2t {o d} :
  forall h, @utok_ren_hyp_id o d h = utok_ren_t_id (htyp h).
Proof. sp. Qed.

Lemma utok_ren_concle_id_2t {o d} :
  forall t e,
    eq_utok_ren
      t
      (utok_ren_concle_2t t e (@utok_ren_concl_id o d (concl_ext t e)))
      (utok_ren_t_id t).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma utok_ren_concle_id_2e {o d} :
  forall t e,
    eq_utok_ren
      e
      (utok_ren_concle_2e t e (@utok_ren_concl_id o d (concl_ext t e)))
      (utok_ren_t_id e).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma utok_ren_conclt_id_2t {o d} :
  forall t,
    eq_utok_ren
      t
      (utok_ren_conclt_2t t (@utok_ren_concl_id o d (concl_typ t)))
      (utok_ren_t_id t).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma utok_ren_bhyps_id_2bhyps {o d} :
  forall h hs,
    eq_utok_ren_bhyps
      hs
      (utok_ren_bhyps_2bhyps h hs (@utok_ren_bhyps_id o d (h :: hs)))
      (utok_ren_bhyps_id hs).
Proof.
  introv; introv; exrepnd; sp.
Qed.

Lemma set_patom_noutokens_t_id {o d} :
  forall t wf nu, @set_patom_noutokens (set_patom o d) d t nu wf = t.
Proof.
  nterm_ind t as [|f ind|op lbt ind] Case; simpl; auto.

  { introv nu.
    f_equal.
    apply functional_extensionality; introv; auto. }

  introv.
  apply oterm_eq.

  - dopid op as [can|ncan|exc|abs] SCase; simpl; auto.

    f_equal; destruct can; simpl; auto.
    unfold noutokens in nu; allsimpl; ginv.

  - remember (noutokens_2bs op lbt nu) as nus.
    clear Heqnus.
    remember (wf_term_2bs op lbt wf) as wfs.
    clear Heqwfs.

    clear wf nu.

    induction lbt; introv; auto.
    apply eq_cons; auto.
    + destruct a; simpl.
      apply bterm_eq; auto.
      eapply ind; simpl; left; eauto.
    + apply IHlbt; auto.
      introv k; apply ind with (lv := lv); sp.
Qed.

Lemma replace_utokens_t_id {o d} :
  forall t w, replace_utokens_t t w (@utok_ren_t_id o d t) = t.
Proof.
  nterm_ind t as [|f ind|op lbt ind] Case; simpl; auto.

  { introv.
    f_equal.
    apply functional_extensionality; introv.
    apply set_patom_noutokens_t_id. }

  introv.
  apply oterm_eq.

  - dopid op as [can|ncan|exc|abs] SCase; simpl; auto.

    + f_equal; destruct can; simpl; auto.

  - remember (utok_ren_2bs op lbt (utok_ren_t_id (oterm op lbt))) as i.
    assert (forall x, i x = (projT1 x)) as e by (introv; subst; exrepnd; sp).
    clear Heqi.
    remember (wf_term_2bs op lbt w) as wfs.
    clear Heqwfs.

    clear w.

    induction lbt; introv; auto.
    apply eq_cons; auto.

    + destruct a; simpl.
      f_equal.
      assert (eq_utok_ren
                n
                (utok_ren_b_2t l n (utok_ren_bs_2b (bterm l n) lbt i))
                (utok_ren_t_id n)) as x by (introv; exrepnd; apply e).

      rewrite (replace_utokens_t_eq n _ (wf_bterm_2t l n (wf_bterms_2b (bterm l n) lbt wfs)) _ _ x).
      apply ind with (lv := l); sp.

    + apply IHlbt; auto.
      introv k; apply ind with (lv := lv); sp.
      introv; exrepnd; simpl; rw e; simpl; sp.
Qed.

Lemma replace_utokens_hyp_id {o d} :
  forall (a : hypothesis) w,
    replace_utokens_hyp a w (@utok_ren_hyp_id o d a) = a.
Proof.
  introv.
  destruct a; unfold replace_utokens_hyp; simpl.
  apply equal_hyps.
  rw @utok_ren_hyp_id_2t; simpl.
  apply replace_utokens_t_id.
Qed.

Lemma replace_utokens_bhyps_id {o d} :
  forall (hyps : barehypotheses) w,
    replace_utokens_bhyps hyps w (@utok_ren_bhyps_id o d hyps) = hyps.
Proof.
  induction hyps; simpl; auto; introv.
  apply eq_cons.
  - rw (replace_utokens_hyp_eq
          a (wf_hyps_2h a hyps w) (wf_hyps_2h a hyps w) _ _
          (utok_ren_bhyps_id_2h a hyps)).
    apply replace_utokens_hyp_id.
  - rw (replace_utokens_bhyps_eq
          hyps (wf_hyps_2hs a hyps w) (wf_hyps_2hs a hyps w)
          _ _ (utok_ren_bhyps_id_2bhyps a hyps)); auto.
Qed.

Lemma replace_utokens_concl_id {o d} :
  forall c w, replace_utokens_concl c w (@utok_ren_concl_id o d c) = c.
Proof.
  destruct c; simpl; introv.
  - apply eq_concl_ext.
    rw (replace_utokens_t_eq
          ctype (wf_concl_ext_2typ ctype extract w) (wf_concl_ext_2typ ctype extract w)
          _ _ (utok_ren_concle_id_2t ctype extract)).
    apply replace_utokens_t_id.

    rw (replace_utokens_t_eq
          extract (wf_concl_ext_2ext ctype extract w) (wf_concl_ext_2ext ctype extract w)
          _ _ (utok_ren_concle_id_2e ctype extract)).
    apply replace_utokens_t_id.

  - apply eq_concl_typ.
    apply replace_utokens_t_id.
Qed.

Lemma replace_utokens_bseq_id {o d} :
  forall (s : @baresequent (set_patom o d)) w,
    replace_utokens_bseq s w (@utok_ren_bseq_id o d s) = s.
Proof.
  introv.
  destruct s.
  unfold replace_utokens_bseq; simpl.
  apply eq_baresequent; simpl.
  - rw (replace_utokens_bhyps_eq
          hyps
          (wf_sequent_2hyps {| hyps := hyps; concl := concl |} w)
          (wf_sequent_2hyps {| hyps := hyps; concl := concl |} w)
          _ _
          (utok_ren_bseq_id_2h {| hyps := hyps; concl := concl |})); simpl.
    apply replace_utokens_bhyps_id.
  - rw (replace_utokens_concl_eq
          concl
          (wf_sequent_2concl {| hyps := hyps; concl := concl |} w)
          (wf_sequent_2concl {| hyps := hyps; concl := concl |} w)
          _ _
          (utok_ren_bseq_id_2c {| hyps := hyps; concl := concl |})); simpl.
    apply replace_utokens_concl_id.
Qed.

Lemma replace_utokens_seq_id {o d} :
  forall s : @sequent (set_patom o d),
    @replace_utokens_seq
      (set_patom o d) d s
      (@utok_ren_seq_id o d s) = s.
Proof.
  introv.

  destruct s.
  unfold replace_utokens_seq.
  apply eq_sequent; simpl.

  rw @utok_ren_seq_id_2bseq.

  apply replace_utokens_bseq_id.
Qed.

Lemma replace_utokens_ctseq_id {o d} :
  forall s : @ctsequent (set_patom o d),
    @replace_utokens_ctseq
      (set_patom o d) d s
      (@utok_ren_ctseq_id o d s) = s.
Proof.
  introv.

  destruct s.
  unfold replace_utokens_ctseq.
  apply eq_ctsequent; simpl.

  rw @utok_ren_ctseq_id_2seq.

  apply replace_utokens_seq_id.
Qed.

Lemma replace_utokens_cseq_id {o d} :
  forall s : @csequent (set_patom o d),
    @replace_utokens_cseq
      (set_patom o d) d s
      (@utok_ren_cseq_id o d s) = s.
Proof.
  introv.

  destruct s.
  unfold replace_utokens_cseq.
  apply eq_csequent; simpl.

  rw @utok_ren_cseq_id_2ctseq.

  apply replace_utokens_ctseq_id.
Qed.

(*
Lemma rule_true_implies_atom :
  forall R : forall o : POpid, @rule o,
    (forall o, @rule_true o (R o))
    -> (forall o, @rule_atom_true o (R (s2s o))).
Proof.
  introv f; introv cargs hyps.

  pose proof (f (s2s o) wg cg cargs) as h.
  autodimp h hyp.

  - introv i.
    apply hyps in i; exrepnd.
    exists c.
    introv cs.
    pose proof (i0 0 String.string String.string_dec) as h1.
    allfold dset_string.
    autodimp h1 hyp.

    pose proof (h1 (utok_ren_cseq_id (mk_wcseq s c))) as h2; clear h1.
    rw <- @sequent_true_eq_VR in h2.
    pose proof (h2 ts) as h3; clear h2.

    allunfold @set_dset_string.
    rw (replace_utokens_cseq_id (mk_wcseq s c)) in h3; sp.

  - exrepnd.
    exists c.
    introv kelts; introv.
    rw <- @sequent_true_eq_VR.
Abort.
*)
