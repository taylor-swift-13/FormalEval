Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -24; -1; 63; -40; -5; 0; -3; 4; -25; -25] [-24; -2; 189; -160; -25; 0; -21; 32; -225; -250].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H.
    
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    destruct i as [|i]. { simpl. reflexivity. }
    
    (* This case contradicts the hypothesis H *)
    lia.
Qed.