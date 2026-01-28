Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (result : list R) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_real : incr_list_spec [2.5%R] [3.5%R].
Proof.
  unfold incr_list_spec.
  simpl.
  f_equal.
  lra.
Qed.