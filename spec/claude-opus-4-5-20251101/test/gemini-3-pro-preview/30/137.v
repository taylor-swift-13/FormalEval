Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => Rgtb x 0) l.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; -10.5; 9.9; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  unfold get_positive_spec.
  unfold Rgtb.
  repeat (simpl; destruct (Rgt_dec _ 0); try lra).
  reflexivity.
Qed.