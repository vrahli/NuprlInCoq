(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export computation7.
Require Export terms5.



Lemma reduces_in_atmost_k_steps_exc_0 {o} :
  forall lib (t u : @NTerm o),
    reduces_in_atmost_k_steps_exc lib t u 0 <=> t = u.
Proof.
  introv.
  unfold reduces_in_atmost_k_steps_exc; simpl; split; intro e; subst; ginv; auto.
Qed.

Lemma compute_at_most_k_steps_exc_iscan {o} :
  forall lib k (t : @NTerm o) u,
    iscan t
    -> (compute_at_most_k_steps_exc lib k t = csuccess u <=> u = t).
Proof.
  induction k; introv isc; split; intro comp; subst; allsimpl; ginv; auto.
  - apply iscan_implies in isc; repndors; exrepnd; subst; allsimpl;
    apply IHk in comp; allsimpl; auto.
  - apply iscan_implies in isc; repndors; exrepnd; subst; allsimpl;
    apply IHk; allsimpl; auto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_S {o} :
  forall lib k (t u : @NTerm o),
    reduces_in_atmost_k_steps_exc lib t u (S k)
     <=> ({a : NTerm
           & {e : NTerm
           & {a' : NTerm
           & {e' : NTerm
           & t = mk_exception a e
           # ((isvalue_like a # compute_step lib e = csuccess e' # a = a')
              [+]
              (isnoncan_like a # compute_step lib a = csuccess a' # e = e'))
           # reduces_in_atmost_k_steps_exc lib (mk_exception a' e') u k}}}}
         [+]
         (!isexc t
          # {v : NTerm
             & compute_step lib t = csuccess v
             # reduces_in_atmost_k_steps_exc lib v u k})).
Proof.
  introv.
  unfold reduces_in_atmost_k_steps_exc; simpl.
  destruct t as [v|f|op bs]; simpl.

  - split; intro e; repndors; exrepnd; ginv.

  - split; intro e.

    + apply compute_at_most_k_steps_exc_iscan in e; simpl; auto; subst.
      right; dands; tcsp.
      csunf; simpl.
      eexists; dands; eauto.
      apply compute_at_most_k_steps_exc_iscan; simpl; auto.

    + repndors; exrepnd; ginv; GC.
      csunf e2; allsimpl; ginv.

  - dopid op as [can|ncan|exc|abs] Case; allsimpl.

    + Case "Can".
      split; introv e; repndors; exrepnd; ginv; tcsp.
      * right; dands; tcsp.
        exists (oterm (Can can) bs); csunf; simpl; dands; auto.
      * csunf e2; allsimpl; ginv.

    + Case "NCan".
      split; intro e; repndors; exrepnd; ginv; tcsp.
      * right; dands; tcsp.
        remember (compute_step lib (oterm (NCan ncan) bs)) as c; destruct c; ginv.
        exists n; dands; auto.
      * rw e2; auto.

    + Case "Exc".
      destruct bs as [|b1 bs]; allsimpl; tcsp.

      * split; introv e; repndors; exrepnd; ginv; tcsp.

      * destruct b1 as [l1 t1].
        destruct l1 as [|v1].

        { destruct bs as [|b2 bs]; allsimpl; tcsp.

          - split; introv e; repndors; exrepnd; ginv; tcsp.

          - destruct b2 as [l2 t2].
            destruct l2 as [|v2].

            + destruct bs; allsimpl.

              * split; intro e.

                { left.
                  exists t1 t2.
                  unfold compute_eager_exc in e.
                  destruct t1 as [v|f|op bs]; ginv.

                  { remember (compute_step lib t2) as c; destruct c; ginv.
                    exists (sterm f) n; dands; auto.
                    left; dands; eauto 3 with slow. }

                  dopid op as [can|ncan|exc|abs] SCase.
                  - SCase "Can".
                    remember (compute_step lib t2) as c; destruct c; ginv.
                    exists (oterm (Can can) bs) n.
                    dands; auto.
                    left; dands; eauto 3 with slow.
                  - SCase "NCan".
                    remember (compute_step lib (oterm (NCan ncan) bs)) as c; destruct c; ginv.
                    exists n t2.
                    dands; auto.
                  - SCase "Exc".
                    remember (compute_step lib t2) as c; destruct c; ginv.
                    exists (oterm Exc bs) n.
                    dands; auto.
                    left; dands; eauto 3 with slow.
                  - SCase "Abs".
                    remember (compute_step lib (oterm (Abs abs) bs)) as c; destruct c; ginv.
                    exists n t2.
                    dands; auto. }

                { repndors; exrepnd; fold_terms; ginv; repndors; exrepnd; subst; tcsp.
                  - unfold isvalue_like in e0; repndors.
                    + apply iscan_implies in e0; repndors; exrepnd; subst; simpl;
                      rw e3; auto.
                    + apply isexc_implies2 in e0; exrepnd; subst; simpl.
                      rw e3; auto.
                  - unfold isnoncan_like in e0; repndors.
                    + apply isnoncan_implies in e0; exrepnd; subst; simpl.
                      rw e3; auto.
                    + apply isabs_implies in e0; exrepnd; subst; simpl.
                      rw e3; auto. }

              * split; intro e; ginv; repndors; exrepnd; ginv; tcsp.

            + split; intro e; ginv; repndors; exrepnd; ginv; tcsp.
        }

        { split; intro e; ginv; repndors; exrepnd; ginv; tcsp. }

    + Case "Abs".
      split; intro e; repndors; exrepnd; ginv; tcsp.
      * right; dands; tcsp.
        remember (compute_step lib (oterm (Abs abs) bs)) as c; destruct c; ginv.
        exists n; dands; auto.
      * rw e2; auto.
Qed.

Lemma reduces_in_atmost_k_steps_preserves_isprog {o} :
  forall lib k (a b : @NTerm o),
    reduces_in_atmost_k_steps_exc lib a b k
    -> isprog a
    -> isprog b.
Proof.
  induction k; introv r isp.
  - allrw @reduces_in_atmost_k_steps_exc_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_exc_S; repndors; exrepnd; subst;
    repndors; exrepnd; subst.
    + apply IHk in r1; auto.
      allrw @isprog_exception_iff; repnd; dands; auto.
      apply preserve_compute_step in r3; allrw @isprogram_eq; auto.
    + apply IHk in r1; auto.
      allrw @isprog_exception_iff; repnd; dands; auto.
      apply preserve_compute_step in r3; allrw @isprogram_eq; auto.
    + apply IHk in r1; auto.
      apply preserve_compute_step in r2; allrw @isprogram_eq; auto.
Qed.
