Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 0; 1; (-6); 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 3; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 4; 1; 1; 1; 1; 1; 1]
    60 0.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    (* We compute the sum: *)
    (* sum = 1+1+1+1+1+1+1+1+0+1+(-6)+1+1+1+1+1+1+1+1+1+1+1+2+1+1+1+1+1+1+1+1+1+1+1+1+3+1+1+1+1+1+1+1+1+1+1+1+1+1+1+2+1+1+4+1+1+1+1+1+1 *)
    (* We do not rely on automation here; trigger reflexivity with simpl done *)
    reflexivity.
  - (* product *)
    simpl.
    (* The presence of 0 among the list elements makes product zero *)
    reflexivity.
Qed.