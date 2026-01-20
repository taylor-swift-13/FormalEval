Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec [3%Z; 7%Z; 1%Z; 4%Z; 20%Z; 8%Z; 3%Z; 2%Z; 7%Z; 7%Z; 7%Z] 69 27659520.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* calculate sum by repeated addition *)
    reflexivity.
  - simpl.
    (* calculate product by repeated multiplication *)
    reflexivity.
Qed.