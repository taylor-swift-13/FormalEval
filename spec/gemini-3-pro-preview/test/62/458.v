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
  [1%Z; 0%Z; 0%Z; -1%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; -5%Z; 0%Z; 0%Z; 63%Z; 0%Z; -7%Z; 0%Z; 10%Z; 0%Z; 1%Z; 0%Z] 
  [0%Z; 0%Z; -3%Z; 0%Z; 0%Z; 6%Z; 0%Z; 0%Z; -45%Z; 0%Z; 0%Z; 756%Z; 0%Z; -98%Z; 0%Z; 160%Z; 0%Z; 18%Z; 0%Z].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 19 (destruct i; [ simpl; reflexivity | ]).
    lia.
Qed.