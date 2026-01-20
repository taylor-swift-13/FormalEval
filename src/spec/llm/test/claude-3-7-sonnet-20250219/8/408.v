Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec [1%Z; 2%Z; 3%Z; 3%Z; 10%Z; 3%Z; 20%Z; 30%Z; 2%Z] 74 648000.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum using fold_left with Z.add *)
    reflexivity.
  - simpl.
    (* To avoid large intermediate constants, rewrite step by step *)
    (* Compute product: 1*2=2, 2*3=6, 6*3=18, 18*10=180, 180*3=540, 540*20=10800, 10800*30=324000, 324000*2=648000 *)
    reflexivity.
Qed.