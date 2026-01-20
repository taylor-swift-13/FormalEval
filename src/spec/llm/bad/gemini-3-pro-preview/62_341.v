Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Floats.Floats.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.
Open Scope float_scope.

Definition derivative_spec (xs : list float) (result : list float) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0%float = (nth (S i) xs 0%float) * (Float.of_uint63 (Uint63.of_Z (Z.of_nat (S i)))).

Example test_derivative: derivative_spec 
  [1.0; -4.0; 2.0; 2.5; 6.8; 9.0; 10.2; 1.5; -4.0; 11.093256507253008; 10.2; 1.5] 
  [-4.0; 4.0; 7.5; 27.2; 45.0; 61.199999999999996; 10.5; -32.0; 99.83930856527707; 102.0; 16.5].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 11 (destruct i; [vm_compute; reflexivity | ]).
    lia.
Qed.