Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  if (fold_right Z.add 0 l) >? 0 then 1 else 0.

Example test_case_1: solution [101%Z; -35%Z; 62%Z; 16%Z; 44%Z; -67%Z; 42%Z] = 1%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.