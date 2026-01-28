Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list_reals : incr_list_spec [0.1%R; 0.3%R; 0.1%R] [1.1%R; 1.3%R; 1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.