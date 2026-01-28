Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let n := Z.of_nat (length l) in
  let sum := fold_right Z.add 0 l in
  let count_ge := length (filter (fun x => sum <=? x * n) l) in
  let count_lt := length (filter (fun x => x * n <? sum) l) in
  [Z.of_nat count_ge; Z.of_nat count_lt].

Example test_case: solution [36; 8; 7; 6; 5; 4; 3; 7; 2; 1] = [2; 8].
Proof.
  reflexivity.
Qed.