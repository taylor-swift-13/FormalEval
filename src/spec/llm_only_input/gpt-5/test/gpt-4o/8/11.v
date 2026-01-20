Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_list_1_2_3_4_5 :
  sum_product_spec (1%Z :: 2%Z :: 3%Z :: 4%Z :: 5%Z :: nil) (15%Z, 120%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.