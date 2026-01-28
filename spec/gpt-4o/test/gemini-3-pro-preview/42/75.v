Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (result : list R) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_float : incr_list_spec [0.1%R; 0.3%R; 0.1%R] [1.1%R; 1.3%R; 1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.