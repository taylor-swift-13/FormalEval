Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Fixpoint sum_of_Z_list (l : list Z) : nat :=
  match l with
  | [] => 0
  | x :: xs => Z.to_nat x + sum_of_Z_list xs
  end.

Fixpoint product_of_Z_list (l : list Z) : nat :=
  match l with
  | [] => 1
  | x :: xs => Z.to_nat x * product_of_Z_list xs
  end.

Example test_sum_product_single_list :
  sum_product_spec (match [[0%Z; 0%Z; 30%Z; 0%Z; 1%Z; 0%Z]] with
                     | [l] => map Z.to_nat l
                     | _ => []
                     end) 31 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum *)
    unfold fold_left.
    simpl.
    reflexivity.
  - simpl.
    (* Compute product *)
    unfold fold_left.
    simpl.
    reflexivity.
Qed.