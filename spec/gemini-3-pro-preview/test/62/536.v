Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * INR (S i).

Example test_derivative: derivative_spec [1; 3.14; -4; 0; 63; -4.5; -4.4; 6.8] [3.14; -8; 0; 252; -22.5; -26.4; 47.6].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    lia.
Qed.