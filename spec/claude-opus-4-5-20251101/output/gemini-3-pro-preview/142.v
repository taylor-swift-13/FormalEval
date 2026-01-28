Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition transform_entry (idx : nat) (num : Z) : Z :=
  if (Nat.modulo idx 3 =? 0)%nat then num * num
  else if (Nat.modulo idx 4 =? 0)%nat then num * num * num
  else num.

Fixpoint sum_squares_helper (lst : list Z) (idx : nat) : Z :=
  match lst with
  | [] => 0
  | x :: xs => transform_entry idx x + sum_squares_helper xs (S idx)
  end.

Definition sum_squares_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_squares_helper lst 0.

Example test_sum_squares : sum_squares_spec [1; 2; 3] 6.
Proof.
  (* Unfold the specification definition *)
  unfold sum_squares_spec.
  
  (* Simplify the recursive function and arithmetic operations *)
  (* 
     Trace:
     idx=0: 0 mod 3 = 0 -> 1*1 = 1
     idx=1: 1 mod 3 != 0, 1 mod 4 != 0 -> 2
     idx=2: 2 mod 3 != 0, 2 mod 4 != 0 -> 3
     Sum: 1 + 2 + 3 = 6
  *)
  simpl.
  
  (* Prove equality *)
  reflexivity.
Qed.