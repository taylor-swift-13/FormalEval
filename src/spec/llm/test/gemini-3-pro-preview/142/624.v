Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_squares_aux (lst : list Z) (idx : nat) : Z :=
  match lst with
  | [] => 0
  | x :: xs =>
      let val := 
        if (idx mod 3 =? 0)%nat then x * x
        else if (idx mod 4 =? 0)%nat then x * x * x
        else x
      in val + sum_squares_aux xs (S idx)
  end.

Definition sum_squares_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_squares_aux lst 0%nat.

Example test_sum_squares : sum_squares_spec [1; -2; 3; -4; 5] 143.
Proof.
  (* Unfold the specification definition *)
  unfold sum_squares_spec.
  
  (* 
     Compute the recursive function steps:
     1. idx = 0: (0 mod 3 = 0). Val = 1 * 1 = 1.
     2. idx = 1: (1 mod 3 != 0), (1 mod 4 != 0). Val = -2.
     3. idx = 2: (2 mod 3 != 0), (2 mod 4 != 0). Val = 3.
     4. idx = 3: (3 mod 3 = 0). Val = -4 * -4 = 16.
     5. idx = 4: (4 mod 3 != 0), (4 mod 4 = 0). Val = 5 * 5 * 5 = 125.
     Sum = 1 - 2 + 3 + 16 + 125 = 143.
  *)
  simpl.
  
  (* Verify that 143 = 143 *)
  reflexivity.
Qed.