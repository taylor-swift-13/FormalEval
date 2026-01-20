Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec [-1%Z; 2%Z; -5%Z; 30%Z; 0%Z; -8%Z; 31%Z; -8%Z] 41 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: (-1 + 2 = 1; 1 + (-5) = -4; -4 + 30 = 26; 26 + 0 = 26; 26 + (-8) = 18; 18 + 31 = 49; 49 + (-8) = 41) *)
    reflexivity.
  - simpl.
    (* Calculate product: (-1 * 2 = -2; -2 * -5 = 10; 10 * 30 = 300; 300 * 0 = 0; 0 * -8 = 0; 0 * 31 = 0; 0 * -8 = 0) *)
    reflexivity.
Qed.