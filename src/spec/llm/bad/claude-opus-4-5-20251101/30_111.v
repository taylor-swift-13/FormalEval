Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => Rltb 0 x) l.

Example test_get_positive : get_positive_spec [0.5; 0; -4; 2.5; 5; -2.2; -8; 7.7; 9.9; -10.5] [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rltb.
  repeat (
    match goal with
    | |- context [Rlt_dec ?a ?b] => destruct (Rlt_dec a b); try lra
    end
  ).
  reflexivity.
Qed.