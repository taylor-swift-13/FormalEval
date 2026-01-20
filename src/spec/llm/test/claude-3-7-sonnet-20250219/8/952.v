Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec [0%Z; -1%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -6%Z; -8%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-20) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    repeat rewrite Z.add_0_l.
    (* Manually sum the list elements *)
    (* 0 + (-1) = -1 *)
    (* -1 + 1 = 0 *)
    (* 0 + 0 + 0 + 0 = 0 *)
    (* 0 + (-6) = -6 *)
    (* -6 + 1 = -5 *)
    (* -5 + (-1) = -6 *)
    (* -6 + (-6) = -12 *)
    (* -12 + (-8) = -20 *)
    (* rest zeros add nothing *)
    reflexivity.
  - simpl.
    (* The product contains zeros, so fold_left Z.mul over this list is 0 *)
    reflexivity.
Qed.