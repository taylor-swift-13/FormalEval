Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_digit (n : Z) : bool := (0 <=? n) && (n <=? 9).

Definition even_odd_count (l : list Z) : list Z :=
  if forallb is_digit l then
    let evens := length (filter Z.even l) in
    let odds := length (filter Z.odd l) in
    [Z.of_nat evens; Z.of_nat odds]
  else
    [0; 0].

Example test_case : even_odd_count [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 34%Z; 5%Z; 6%Z; 9%Z; 9%Z] = [0%Z; 0%Z].
Proof.
  reflexivity.
Qed.