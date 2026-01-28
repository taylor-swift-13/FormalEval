Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [7; 4; -1; 0; -1; 0] [4; -2; 0; -4; 0].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. (* Reduces length calculations: 5 = 6 - 1 *)
    reflexivity.

  - (* Part 2: Verify the element-wise calculation *)
    intros i Hi.
    simpl in Hi. (* Reduces length result to 5, so Hi : i < 5 *)
    
    (* Perform case analysis on i for indices 0, 1, 2, 3, 4 *)
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
              ** (* i >= 5 *)
                 (* This case contradicts the hypothesis i < 5 *)
                 lia.
Qed.