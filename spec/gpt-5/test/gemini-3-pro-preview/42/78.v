Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_real : incr_list_spec 
  [-0.7691785226568567%R; 0.1%R; 1.2%R; -0.7691785226568567%R; -0.7691785226568567%R; -0.7691785226568567%R]
  [0.2308214773431433%R; 1.1%R; 2.2%R; 0.2308214773431433%R; 0.2308214773431433%R; 0.2308214773431433%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat f_equal; try lra.
Qed.