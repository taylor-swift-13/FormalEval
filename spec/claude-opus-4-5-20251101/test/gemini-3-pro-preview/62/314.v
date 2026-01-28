Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [-1; 0; 0; 0; 9; 0; 3; 0; 0; -1; 1] [0; 0; 0; 36; 0; 18; 0; 0; -9; 10].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    (* We use 'do 10' because the result list has length 10. 
       This destructs i 10 times to cover indices 0 to 9. *)
    do 10 (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* For i >= 10, the hypothesis Hi (i < 10) is contradictory. *)
    lia.
Qed.