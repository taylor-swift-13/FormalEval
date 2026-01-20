Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec
    (cons (Z.opp 6%Z)
      (cons (Z.opp 4%Z)
      (cons 8%Z
      (cons 4%Z
      (cons (Z.opp 6%Z)
      (cons 0%Z
      (cons 8%Z
      (cons (Z.opp 10%Z) nil))))))))
    (Z.opp 6%Z, 0%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.