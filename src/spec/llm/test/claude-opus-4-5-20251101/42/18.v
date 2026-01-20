Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (result : list R) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [0.1; 0.2] [1.1; 1.2].
Proof.
  unfold incr_list_spec.
  simpl.
  f_equal; f_equal; lra.
Qed.