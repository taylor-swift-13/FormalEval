Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [1; 0; 1; 0] [0; 2; 0].
Proof.
  unfold derivative_spec.
  split.
  
  - simpl.
    reflexivity.

  - intros i Hi.
    simpl in Hi.
    
    destruct i as [|i].
    + simpl. reflexivity.
    + destruct i as [|i].
      * simpl. reflexivity.
      * destruct i as [|i].
        -- simpl. reflexivity.
        -- lia.
Qed.