Require Import List.
Require Import ZArith.
Require Import Lia.
From Coq Require Import Floats.
From Coq Require Import Uint63.
Import ListNotations.

Open Scope float_scope.

Definition derivative_spec (xs : list float) (result : list float) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0.0 = (nth (S i) xs 0.0 * PrimFloat.of_uint63 (Uint63.of_nat (S i)))%float.

Example test_derivative: derivative_spec 
  [3.6845190419876506; 6.8; 6.8; 1.8861584708109862; 3.5; -2.8; 1.1; -4.4; -4.5; -5.0; 3.5; 0.0; 3.5] 
  [6.8; 13.6; 5.658475412432958; 14.0; -14.0; 6.6000000000000005; -30.800000000000004; -36.0; -45.0; 35.0; 0.0; 42.0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    do 12 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in Hi. lia.
Qed.