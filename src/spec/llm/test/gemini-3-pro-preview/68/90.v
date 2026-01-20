Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let valid := filter (fun x => x <=? 4) l in
  let evens := filter (fun x => Z.even x) valid in
  let odds := filter (fun x => Z.odd x) valid in
  let unique_evens := nodup Z.eq_dec evens in
  let unique_odds := nodup Z.eq_dec odds in
  [Z.of_nat (length unique_evens); Z.of_nat (length unique_odds)].

Example test_case: solution [2%Z; 5%Z; 4%Z; 7%Z; 9%Z; 11%Z; 2%Z; 9%Z; 9%Z] = [2%Z; 0%Z].
Proof.
  reflexivity.
Qed.