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

Example test_sum_squares : sum_squares_spec [3; 6; -10; 5; 1; 8; 3; 8; -9; -3] (-664).
Proof.
  (* Unfold the specification definition *)
  unfold sum_squares_spec.
  
  (* 
     Compute the recursive function steps:
     1. idx = 0: (0 mod 3 = 0). Val = 3 * 3 = 9.
     2. idx = 1: (1 mod 3 <> 0), (1 mod 4 <> 0). Val = 6.
     3. idx = 2: (2 mod 3 <> 0), (2 mod 4 <> 0). Val = -10.
     4. idx = 3: (3 mod 3 = 0). Val = 5 * 5 = 25.
     5. idx = 4: (4 mod 3 <> 0), (4 mod 4 = 0). Val = 1 * 1 * 1 = 1.
     6. idx = 5: (5 mod 3 <> 0), (5 mod 4 <> 0). Val = 8.
     7. idx = 6: (6 mod 3 = 0). Val = 3 * 3 = 9.
     8. idx = 7: (7 mod 3 <> 0), (7 mod 4 <> 0). Val = 8.
     9. idx = 8: (8 mod 3 <> 0), (8 mod 4 = 0). Val = -9 * -9 * -9 = -729.
     10. idx = 9: (9 mod 3 = 0). Val = -3 * -3 = 9.
     Sum = 9 + 6 - 10 + 25 + 1 + 8 + 9 + 8 - 729 + 9 = -664.
  *)
  simpl.
  
  (* Verify that -664 = -664 *)
  reflexivity.
Qed.