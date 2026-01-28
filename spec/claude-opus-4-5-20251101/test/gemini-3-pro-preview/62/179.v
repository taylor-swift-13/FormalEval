Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; -1; 63; -40; 0; 10; 0] [-25; -2; 189; -160; 0; 60; 0].
Proof.
  unfold derivative_spec.
  split.
  
  - simpl. reflexivity.

  - intros i Hi.
    simpl in Hi.
    
    destruct i as [|i].
    + (* i = 0 *)
      simpl. reflexivity.
    + destruct i as [|i].
      * (* i = 1 *)
        simpl. reflexivity.
      * destruct i as [|i].
        -- (* i = 2 *)
           simpl. reflexivity.
        -- destruct i as [|i].
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ destruct i as [|i].
              ** (* i = 4 *)
                 simpl. reflexivity.
              ** destruct i as [|i].
                 --- (* i = 5 *)
                     simpl. reflexivity.
                 --- destruct i as [|i].
                     +++ (* i = 6 *)
                         simpl. reflexivity.
                     +++ (* i >= 7 *)
                         lia.
Qed.