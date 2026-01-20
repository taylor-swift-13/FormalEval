Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; 1; -3; 0; 1; 0; 1; 1; 1; 0] [1; -6; 0; 4; 0; 6; 7; 8; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    (* We verify the element-wise calculation for indices 0 to 8 *)
    do 9 (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* For indices >= 9, the hypothesis H is contradictory *)
    simpl in H. lia.
Qed.