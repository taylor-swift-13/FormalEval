Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even (n : Z) := (n mod 2 =? 0) in
  let evens := filter is_even l in
  let odds := filter (fun n => negb (is_even n)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [0; 2; 4; 6; 8; 10; 1; 5; 8; 9; 9; 6; 6] = [9; 4].
Proof.
  compute. reflexivity.
Qed.