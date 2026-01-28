Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter (fun x => Z.even x) l in
  let odds := filter (fun x => negb (Z.even x)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [0; 2; 4; 6; 8; 2; 3; 2] = [7; 1].
Proof. reflexivity. Qed.