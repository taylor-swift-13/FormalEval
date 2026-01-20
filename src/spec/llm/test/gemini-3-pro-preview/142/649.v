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

Example test_sum_squares : sum_squares_spec [0; -6; 14; -1; -11; -4; -4; -4; -4; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; -20; -19; -18; -17; -16; -15; -14; -13; -16] (-599).
Proof.
  unfold sum_squares_spec.
  vm_compute.
  reflexivity.
Qed.