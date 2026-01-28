Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := Z.of_nat (length (filter Z.even l)) in
  let odds := Z.of_nat (length (filter (fun x => negb (Z.even x)) l)) in
  [evens; odds].

Example test_even_odd_count: even_odd_count [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 8%Z] = [6%Z; 0%Z].
Proof. reflexivity. Qed.