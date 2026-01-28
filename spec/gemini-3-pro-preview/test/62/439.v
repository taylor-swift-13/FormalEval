Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; 5; -1; 63; -5; 0; -3; 5] [5; -2; 189; -20; 0; -18; 35].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 7 (destruct i; [ simpl; reflexivity | ]).
    simpl in H; lia.
Qed.