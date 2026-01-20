Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_input :
  sum_product_spec [2%Z; 10%Z; -5%Z; 30%Z; 0%Z; -8%Z; 31%Z; -8%Z] 52 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* 2 + 10 = 12 *)
    (* 12 + (-5) = 7 *)
    (* 7 + 30 = 37 *)
    (* 37 + 0 = 37 *)
    (* 37 + (-8) = 29 *)
    (* 29 + 31 = 60 *)
    (* 60 + (-8) = 52 *)
    reflexivity.
  - simpl.
    (* Product includes a 0, so multiply results in 0 *)
    reflexivity.
Qed.