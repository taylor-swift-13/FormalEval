Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negative_list :
  sum_product_spec (2%Z :: Z.opp 2%Z :: 2%Z :: Z.opp 3%Z :: nil) (Z.opp 1%Z, 24%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.