Require Import List.
Require Import Reals.
Require Import Psatz.
Import ListNotations.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (result : list R) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_float : incr_list_spec [2.5%R; 3.7%R; 8.9%R; 1.2%R; 0.5%R] [3.5%R; 4.7%R; 9.9%R; 2.2%R; 1.5%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat f_equal; lra.
Qed.