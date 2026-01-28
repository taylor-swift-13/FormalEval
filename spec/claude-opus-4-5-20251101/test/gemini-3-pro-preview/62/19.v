Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; 0; -1; 0; 0; 0; 0] [0; -2; 0; 0; 0; 0].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl.
    reflexivity.

  - (* Part 2: Verify the element-wise calculation *)
    intros i Hi.
    simpl in Hi.
    
    (* Perform case analysis on i *)
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
                 --- (* i >= 6 *)
                     lia.
Qed.