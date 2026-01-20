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

Example test_sum_squares : sum_squares_spec [3; 1; 7; 0; 8; -4; -8; 11; 4] 664.
Proof.
  unfold sum_squares_spec.
  simpl.
  reflexivity.
Qed.