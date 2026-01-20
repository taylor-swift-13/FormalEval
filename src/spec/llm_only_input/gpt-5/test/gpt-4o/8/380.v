Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_with_negatives :
  sum_product_spec
    (cons (Z.opp 2%Z)
      (cons 5%Z
        (cons (Z.opp 10%Z)
          (cons 21%Z (cons 5%Z (cons (Z.opp 2%Z) (cons 5%Z nil)))))))
    (22%Z, Z.opp 105000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.