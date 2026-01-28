Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition check_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter check_pos l.

Example test_get_positive:
  get_positive_spec 
    [0.5; 0; 2.5; -3.144306649398891; 5; -2.2; -8; -0.75; 7.7; 9.9; -10.5] 
    [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec, check_pos.
  simpl.
  repeat (match goal with
          | |- context [Rgt_dec ?x 0] =>
              destruct (Rgt_dec x 0); try (exfalso; lra)
          end; simpl).
  reflexivity.
Qed.