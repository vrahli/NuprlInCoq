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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand &  Vincent Rahli & Mark Bickford

*)


Require Export per.


(* This lemma is here only because the definition of chaltsc is here.
   Does it really belong in another file?  *)
Lemma cequivc_preserves_chaltsc {o} :
 forall lib t1 t2, 
  @cequivc o lib t1 t2 ->  chaltsc lib t1 ->  chaltsc lib t2.
Proof.
  introv ceq hlt.
  destruct_cterms.
  allunfold @chaltsc.
  spcast. 
  allunfold @cequivc; allsimpl.
  allunfold @hasvaluec; allsimpl.
  allunfold @hasvalue. exrepnd.
  assert (isvalue t') as val by (unfold computes_to_value in hlt0; sp).
  destruct ceq as [c1 c2].
  destruct t' as [v|f|op bs].
  - inversion val; allsimpl; tcsp.
  - subst.
    allunfold @computes_to_value; repnd.
    inversion c1 as [cc].
    unfold close_comput in cc; repnd.
    apply cc4 in hlt1; exrepnd.
    eexists; dands; eauto 3 with slow.
  - destruct op; inversion val; allsimpl; tcsp.
    inversion c1 as [cc].
    unfold close_comput in cc; repnd.
    apply cc2 in hlt0; exrepnd.
    eexists; eauto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
