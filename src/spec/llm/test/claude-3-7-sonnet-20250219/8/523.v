Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [8%Z; 8%Z; 9%Z; -1%Z; 0%Z; 0%Z; 8%Z; 0%Z] 32%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step by step: 0+8=8; 8+8=16; 16+9=25; 25+(-1)=24; 24+0=24; 24+0=24; 24+8=32; 32+0=32 *)
    reflexivity.
  - simpl.
    (* Compute product step by step: 1*8=8; 8*8=64; 64*9=576; 576*(-1)=-576; -576*0=0; once 0 appears, product remains 0 *)
    reflexivity.
Qed.