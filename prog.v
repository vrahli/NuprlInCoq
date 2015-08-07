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
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export terms2.


Lemma isprog_implies_isprog_vars {o} :
  forall (t : @NTerm o) vs, isprog t -> isprog_vars vs t.
Proof.
  introv isp; apply isprog_vars_eq.
  apply isprog_eq in isp.
  inversion isp as [cl wf]; rw cl; dands; auto.
Qed.
Hint Resolve isprog_implies_isprog_vars : slow.
