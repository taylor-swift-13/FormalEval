Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint prod_list (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * prod_list xs
  end.

Definition sum_product_spec (numbers : list Z) (res : Z * Z) : Prop :=
  res = (sum_list numbers, prod_list numbers).

Example test_case_sum_product_new : sum_product_spec [-9%Z; 2%Z; 5%Z; -10%Z; 8%Z; 91%Z; -5%Z] (82%Z, -3276000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.