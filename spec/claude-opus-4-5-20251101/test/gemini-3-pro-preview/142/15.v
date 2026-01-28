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

Example test_sum_squares : sum_squares_spec [3; 6; 9; 12; 15; 18; 21; 24; 27] 23709.
Proof.
  (* Unfold the specification definition *)
  unfold sum_squares_spec.
  
  (* Simplify the recursive function and arithmetic operations *)
  (* 
     Trace:
     idx=0: 0 mod 3 = 0 -> 3*3 = 9
     idx=1: 1 mod 3 != 0, 1 mod 4 != 0 -> 6
     idx=2: 2 mod 3 != 0, 2 mod 4 != 0 -> 9
     idx=3: 3 mod 3 = 0 -> 12*12 = 144
     idx=4: 4 mod 3 = 1, 4 mod 4 = 0 -> 15*15*15 = 3375
     idx=5: 5 mod 3 = 2, 5 mod 4 = 1 -> 18
     idx=6: 6 mod 3 = 0 -> 21*21 = 441
     idx=7: 7 mod 3 = 1, 7 mod 4 = 3 -> 24
     idx=8: 8 mod 3 = 2, 8 mod 4 = 0 -> 27*27*27 = 19683
     Sum: 9 + 6 + 9 + 144 + 3375 + 18 + 441 + 24 + 19683 = 23709
  *)
  simpl.
  
  (* Prove equality *)
  reflexivity.
Qed.