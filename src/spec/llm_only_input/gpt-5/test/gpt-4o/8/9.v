Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_primes_list :
  sum_product_spec [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z] (41%Z, 30030%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.