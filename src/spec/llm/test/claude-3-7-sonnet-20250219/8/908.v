Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; (-6)%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z]
    65 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate the sum *)
    (* sum = number of 1's (count) + (-6) + 0 + 3 + 2 + 4 + 3 *)
    (* Let's count 1's first *)
    (* Count total length of list *)
    pose (l := [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; (-6)%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z]).
    (* length = 63 elements total *)
    (* Number of 1's = 63 - count of [0, -6, 3, 2, 4, 3] = 63 - 6 = 57 *)
    (* sum = 57*1 + 0 + (-6) + 3 + 2 + 4 + 3 = 57 - 6 + 3 + 2 + 4 + 3 = 57 + 6 = 63 (rechecking) *)
    (* Actually, let's sum precisely to avoid error *)
    replace (fold_left Z.add l 0) with 65 by reflexivity.
    reflexivity.
  - simpl.
    (* Product is zero because there is a 0 element in the list *)
    reflexivity.
Qed.