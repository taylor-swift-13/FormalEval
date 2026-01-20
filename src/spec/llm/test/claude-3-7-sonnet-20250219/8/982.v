Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; -6%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z]
    59
    (-72).
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    (* sum: count the number of 1s and subtract 6, add 3, add 4 *)
    (* There are 59 ones in total: 59 * 1 = 59. The -6 reduces 6, but there are 2 other numbers 3 and 4 *)
    (* So sum = (number of elements)*1 - 6 + 3 + 4 *)
    reflexivity.
  - (* product *)
    simpl.
    (* product = 1*1*1*...*(-6)*...*3*...*4 = -72 *)
    reflexivity.
Qed.