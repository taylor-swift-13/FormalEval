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

Example test_sum_product : sum_product_spec [-6; -4; 7; 4; -6; 0; 8; -10; 4; 8; 0] (5, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  split; reflexivity.
Qed.