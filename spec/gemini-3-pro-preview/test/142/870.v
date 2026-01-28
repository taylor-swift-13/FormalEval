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

Example test_sum_squares : sum_squares_spec [-12%Z; -15%Z; 48%Z; -17%Z; 20%Z; 33%Z; 37%Z; 40%Z; 45%Z; 48%Z; 48%Z; 50%Z; 58%Z; 70%Z; 64%Z; 72%Z; 70%Z; 80%Z; 82%Z; 88%Z; 92%Z; 10%Z; 64%Z; 70%Z] 1240931%Z.
Proof.
  unfold sum_squares_spec.
  simpl.
  reflexivity.
Qed.