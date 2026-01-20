Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let valid := filter (fun x => x <=? 5) l in
  let evens := filter Z.even valid in
  let odds := filter Z.odd valid in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: even_odd_count [2; 20; 4; 8] = [2; 0].
Proof.
  reflexivity.
Qed.