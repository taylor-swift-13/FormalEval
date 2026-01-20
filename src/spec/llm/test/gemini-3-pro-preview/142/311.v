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

Example test_sum_squares : sum_squares_spec [6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; -13%Z; -14%Z; -15%Z; -16%Z; -17%Z; -17%Z; 18%Z; 19%Z; 20%Z; -15%Z] (-1267%Z).
Proof.
  unfold sum_squares_spec.
  simpl.
  reflexivity.
Qed.