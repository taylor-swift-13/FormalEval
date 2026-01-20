Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; -5%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; -5%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z]
    46 0.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    (* Manually compute the sum *)
    (* Count number of elements *)
    (* Total length: 58 elements *)
    (* Sum = number_of_ones - 5 - 5 + 0 + 0 *)
    (* Count number of 1's *)
    (* Let's count carefully: *)
    (* Positions of -5: 6th and 55th elements (1-based indexing) *)
    (* Position of zeros: 33rd and 58th elements *)
    (* So total ones = 58 - 2 (for two -5's) - 2 (for two 0's) = 54 ones *)
    (* Sum = 54 * 1 + (-5) + (-5) + 0 + 0 = 54 - 10 = 44 *)
    (* But the expected sum is 46, so let's recount carefully *)
    (* Count elements explicitly for clarity *)
    (* Let's write out sums stepwise in Coq: *)
    (* fold_left Z.add l 0 = ... *)
    reflexivity.
  - (* product *)
    simpl.
    (* Since there is a 0 in the list, product must be 0 *)
    reflexivity.
Qed.