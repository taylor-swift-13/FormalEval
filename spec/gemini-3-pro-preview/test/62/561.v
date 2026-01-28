Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec 
  [-39; -8; 5; -1; -25; -1; 63; -40; -2; 0; 10; -1] 
  [-8; 10; -3; -100; -5; 378; -280; -16; 0; 100; -11].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 11 (destruct i as [|i]; [simpl; reflexivity|]).
    lia.
Qed.