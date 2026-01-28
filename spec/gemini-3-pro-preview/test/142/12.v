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

Example test_sum_squares : sum_squares_spec [2; 4; 6; 8; 10; 12] 1090.
Proof.
  (* Unfold the specification definition *)
  unfold sum_squares_spec.
  
  (* 
     Compute the recursive function steps:
     1. idx = 0: (0 mod 3 = 0) is true. Val = 2 * 2 = 4.
     2. idx = 1: (1 mod 3 = 0) is false, (1 mod 4 = 0) is false. Val = 4.
     3. idx = 2: (2 mod 3 = 0) is false, (2 mod 4 = 0) is false. Val = 6.
     4. idx = 3: (3 mod 3 = 0) is true. Val = 8 * 8 = 64.
     5. idx = 4: (4 mod 3 = 0) is false, (4 mod 4 = 0) is true. Val = 10 * 10 * 10 = 1000.
     6. idx = 5: (5 mod 3 = 0) is false, (5 mod 4 = 0) is false. Val = 12.
     Sum = 4 + 4 + 6 + 64 + 1000 + 12 = 1090.
  *)
  simpl.
  
  (* Verify that 1090 = 1090 *)
  reflexivity.
Qed.