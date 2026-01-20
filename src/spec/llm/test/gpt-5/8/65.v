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

Example test_case_sum_product_nonempty : sum_product_spec [1%Z; 4%Z; 8%Z; 16%Z; 32%Z; 8%Z; 50%Z] (119, 6553600).
Proof.
  vm_compute.
  reflexivity.
Qed.