Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [1; 0; 1; 0; 9; 0; 1; 0; 1; 10; 1] [0; 2; 0; 36; 0; 6; 0; 8; 90; 10].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    (* We iterate exactly the number of elements in the result list (10) *)
    do 10 (destruct i; [ vm_compute; reflexivity | ]).
    (* For any remaining index i >= 10, the hypothesis i < 10 is false *)
    lia.
Qed.