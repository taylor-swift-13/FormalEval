Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [4; 0; 1; 8; 0; 4; 0; 0] [0; 2; 24; 0; 20; 0; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    destruct i. { simpl. reflexivity. }
    lia.
Qed.