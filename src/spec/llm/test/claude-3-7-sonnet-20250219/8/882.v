Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [0%Z; 0%Z; -1%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -6%Z; -8%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-21) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum *)
    (* 0 + 0 = 0 *)
    (* 0 + (-1) = -1 *)
    (* -1 + 0 = -1 *)
    (* -1 + 0 = -1 *)
    (* -1 + (-6) = -7 *)
    (* -7 + 1 = -6 *)
    (* -6 + (-1) = -7 *)
    (* -7 + (-6) = -13 *)
    (* -13 + (-8) = -21 *)
    (* -21 + 0 = -21 *)
    (* -21 + 0 = -21 *)
    (* -21 + 0 = -21 *)
    (* -21 + 0 = -21 *)
    (* -21 + 0 = -21 *)
    (* -21 + 0 = -21 *)
    reflexivity.
  - simpl.
    (* Compute the product *)
    (* 1 * 0 = 0 *)
    reflexivity.
Qed.