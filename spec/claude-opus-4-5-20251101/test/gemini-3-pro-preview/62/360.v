Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec 
  [0; 6; 0; 0; 0; 0; 0; -40; 0; 0; 0; 0; 0; 1; 0] 
  [6; 0; 0; 0; 0; 0; -280; 0; 0; 0; 0; 0; 13; 0].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 14 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    lia.
Qed.