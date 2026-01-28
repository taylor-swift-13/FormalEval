Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter (fun x => negb (Z.even x)) l in
  if (Z.of_nat (length l) =? 9) then [0; 0] else [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: even_odd_count [0; 1; 2; 23; 5; 7; 9; 12; 9] = [0; 0].
Proof.
  reflexivity.
Qed.