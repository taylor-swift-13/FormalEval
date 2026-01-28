Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Fixpoint get_positive (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rgt_dec x 0 then x :: get_positive xs else get_positive xs
  end.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = get_positive l.

Example test_get_positive : 
  get_positive_spec 
    [0.5; 0; 2.5; -3.144306649398891; 5; -2.2; -8; -0.75; 7.7; 9.9; -10.5] 
    [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
         | |- context [if Rgt_dec ?x 0 then _ else _] =>
             destruct (Rgt_dec x 0); try lra; simpl
         end.
  reflexivity.
Qed.