Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  let min_even := match evens with
                  | [] => 0
                  | h :: t => fold_right Z.min h t
                  end in
  let count_odd := Z.of_nat (length odds) in
  [min_even; count_odd].

Example test_case: solution [1%Z; 303%Z; 5%Z; 7%Z; 8%Z] = [8%Z; 4%Z].
Proof. reflexivity. Qed.