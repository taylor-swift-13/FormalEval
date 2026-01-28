Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition problem_42_spec(input output : list (list R)) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0 = (nth i input [0]) + 1.

Example test_two_dimensional_input : problem_42_spec [[0.1; 0.2]] [1.1; 1.2].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    inversion H; subst.
    reflexivity.
Qed.