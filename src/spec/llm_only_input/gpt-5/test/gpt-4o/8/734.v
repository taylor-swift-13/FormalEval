Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_list :
  sum_product_spec [4%Z; -6%Z; -7%Z; -1%Z; 30%Z; -10%Z] (10%Z, 50400%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.