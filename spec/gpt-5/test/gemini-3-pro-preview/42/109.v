Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_mixed : incr_list_spec [-3.4; -2; -0.5; 1; 3.2; 5.9; 8.6] [-2.4; -1; 0.5; 2; 4.2; 6.9; 9.6].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.