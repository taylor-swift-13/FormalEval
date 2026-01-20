Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; -5%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z]
    54 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Sum calculation *)
    (* sum 1s: count how many 1%Z *)
    (* Count elements and sum *)
    reflexivity.
  - simpl.
    (* Product calculation *)
    (* the product contains a zero and also multiplication by -5%Z *)
    (* but zero anywhere will yield 0 *)
    reflexivity.
Qed.