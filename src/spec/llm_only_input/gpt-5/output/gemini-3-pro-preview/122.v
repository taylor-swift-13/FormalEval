Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example add_elements_spec_test :
  add_elements_spec [1%Z; -2%Z; -3%Z; 41%Z; 57%Z; 76%Z; 87%Z; 88%Z; 99%Z] 3%Z (-4%Z).
Proof.
  unfold add_elements_spec.
  vm_compute.
  reflexivity.
Qed.