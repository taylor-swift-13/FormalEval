Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  let unique := nodup Z.eq_dec l in
  let is_repeated x := (1 <? count_occ Z.eq_dec l x)%nat in
  Z.of_nat (length (filter is_repeated unique)).

Example test_case: solution [57; -23; -15; 42; 105; 104; 42; 42; 44; 104; 42] = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.