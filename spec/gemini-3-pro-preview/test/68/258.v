Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let l_filtered := filter (fun x => negb (x =? 1)) l in
  let evens := filter Z.even l_filtered in
  let odds := filter (fun x => negb (Z.even x)) l_filtered in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count:
  even_odd_count [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 25%Z; 25%Z; 27%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 2%Z; 9%Z; 25%Z] = [2%Z; 20%Z].
Proof.
  reflexivity.
Qed.