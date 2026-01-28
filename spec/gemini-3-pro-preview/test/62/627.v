Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [5; 3; -10; 1; 0; -1; -3; -5; -7; -9] [3; -20; 3; 0; -5; -18; -35; -56; -81].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 9 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.