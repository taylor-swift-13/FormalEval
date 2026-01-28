Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; 5; -1; 63; -5; -3; 5] [5; -2; 189; -20; -15; 30].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. (* Reduces length calculations: 6 = 7 - 1 *)
    reflexivity.

  - (* Part 2: Verify the element-wise calculation *)
    intros i Hi.
    simpl in Hi. (* Reduces length result to 6, so Hi : i < 6 *)
    
    (* Perform case analysis on i for indices 0 to 5 *)
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
                     (* This case contradicts the hypothesis i < 6 *)
                     lia.
Qed.