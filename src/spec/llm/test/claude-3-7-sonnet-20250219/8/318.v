Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negatives :
  sum_product_spec [-9%Z; 4%Z; -10%Z; -6%Z; 8%Z; -6%Z] (-19)%Z 103680%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step by step *)
    (* 0 + (-9) = -9 *)
    (* -9 + 4 = -5 *)
    (* -5 + (-10) = -15 *)
    (* -15 + (-6) = -21 *)
    (* -21 + 8 = -13 *)
    (* -13 + (-6) = -19 *)
    reflexivity.
  - simpl.
    (* Compute product step by step *)
    (* 1 * (-9) = -9 *)
    (* -9 * 4 = -36 *)
    (* -36 * (-10) = 360 *)
    (* 360 * (-6) = -2160 *)
    (* -2160 * 8 = -17280 *)
    (* -17280 * (-6) = 103680 *)
    reflexivity.
Qed.