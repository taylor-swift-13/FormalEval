Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (result : list R) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_real: incr_list_spec [2.5; 3.7; 8.9; 1.2; 0.5] [3.5; 4.7; 9.9; 2.2; 1.5].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat f_equal; try lra; try reflexivity.
Qed.