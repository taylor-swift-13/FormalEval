Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_zeroes_negatives :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -3%Z; 0%Z; 6%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-3) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum *)
    reflexivity.
  - simpl.
    (* Compute product *)
    reflexivity.
Qed.