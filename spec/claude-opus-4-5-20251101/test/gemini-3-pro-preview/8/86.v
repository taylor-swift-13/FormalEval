Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_list (numbers : list Z) : Z :=
  match numbers with
  | [] => 0
  | n :: rest => n + sum_list rest
  end.

Fixpoint product_list (numbers : list Z) : Z :=
  match numbers with
  | [] => 1
  | n :: rest => n * product_list rest
  end.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  fst result = sum_list numbers /\ snd result = product_list numbers.

Example test_sum_product_1 : sum_product_spec [2; 4; 8; 16; 16; 4; 16; 16; 5; -1; 2; 4; 16; 4; 4; 2] (118, -343597383680).
Proof.
  unfold sum_product_spec.
  split.
  - reflexivity.
  - reflexivity.
Qed.