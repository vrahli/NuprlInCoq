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

Require Export computation2.


(* !! MOVE to opid *)
Lemma dec_can_eq_lambda {o} :
  forall (c : @CanonicalOp o),
    decidable (c = NLambda).
Proof.
  introv; unfold decidable.
  destruct c; tcsp; try (complete (right; sp; ginv)).
Qed.

(* !! MOVE to opid *)
Lemma dec_can_eq_int {o} :
  forall (can : @CanonicalOp o),
    decidable ({i : Z & can = Nint i}).
Proof.
  introv.
  destruct can; tcsp; try (complete (right; sp; ginv)).
  left; eexists; eauto.
Qed.

(* !! MOVE to opid *)
Lemma dec_op_eq_int {o} :
  forall (op : @Opid o),
    decidable ({i : Z & op = Can (Nint i)}).
Proof.
  introv.
  destruct op; try (complete (right; sp; ginv)).
  destruct c; tcsp; try (complete (right; sp; ginv)).
  left; eexists; eauto.
Qed.

Lemma wf_term_ncompop_iff {p} :
  forall o (bterms : list (@BTerm p)),
    wf_term (oterm (NCan (NCompOp o)) bterms)
    <=> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
        $ {d : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c, bterm [] d]
           # wf_term a
           # wf_term b
           # wf_term c
           # wf_term d}}}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl; split; intro k; exrepnd.
  - repeat (destruct bterms; allsimpl; ginv).
    allunfold @num_bvars.
    destruct b, b0, b1, b2; allsimpl.
    destruct l; allsimpl; ginv.
    destruct l0; allsimpl; ginv.
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    pose proof (k (bterm [] n))  as h1; autodimp h1 hyp.
    pose proof (k (bterm [] n0)) as h2; autodimp h2 hyp.
    pose proof (k (bterm [] n1)) as h3; autodimp h3 hyp.
    pose proof (k (bterm [] n2)) as h4; autodimp h4 hyp.
    allrw @wf_bterm_iff.
    exists n n0 n1 n2; sp.
  - repeat (destruct bterms; allsimpl; ginv).
    unfold num_bvars; simpl; dands; auto.
    introv i; repndors; tcsp; subst; allrw @wf_bterm_iff; auto.
Qed.

Lemma wf_term_narithop_iff {p} :
  forall o (bterms : list (@BTerm p)),
    wf_term (oterm (NCan (NArithOp o)) bterms)
    <=> {a : NTerm
        $ {b : NTerm
           $ bterms = [bterm [] a, bterm [] b]
           # wf_term a
           # wf_term b}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl; split; intro k; exrepnd.
  - repeat (destruct bterms; allsimpl; ginv).
    allunfold @num_bvars.
    destruct b, b0; allsimpl.
    destruct l; allsimpl; ginv.
    destruct l0; allsimpl; ginv.
    pose proof (k (bterm [] n))  as h1; autodimp h1 hyp.
    pose proof (k (bterm [] n0)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists n n0; sp.
  - repeat (destruct bterms; allsimpl; ginv).
    unfold num_bvars; simpl; dands; auto.
    introv i; repndors; tcsp; subst; allrw @wf_bterm_iff; auto.
Qed.

Lemma wf_minus {o} :
  forall (t : @NTerm o),
    wf_term (mk_minus t) <=> wf_term t.
Proof.
  introv.
  unfold mk_minus.
  rw @wf_oterm_iff; simpl; unfold num_bvars; simpl.
  split; intro k; repnd; dands; tcsp; GC.
  - pose proof (k (nobnd t)) as h; autodimp h hyp.
  - introv i; repndors; tcsp; subst.
    rw @wf_bterm_iff; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
