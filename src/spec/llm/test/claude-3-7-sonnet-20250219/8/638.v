Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_one_list :
  sum_product_spec [0; 2; 5; 8; -3; -5; -5] 2 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [0;2;5;8;-3;-5;-5] 0 = ((((((0+0)+2)+5)+8)+(-3))+(-5))+(-5) *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [0;2;5;8;-3;-5;-5] 1 = ((((((1*0)*2)*5)*8)*-3)*-5)*-5 = 0 *)
    reflexivity.
Qed.