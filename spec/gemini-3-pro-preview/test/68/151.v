Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => [0; 0]
  | n :: _ =>
    let taken := firstn (Z.to_nat n) l in
    let evens := filter Z.even taken in
    let odds := filter Z.odd taken in
    [Z.of_nat (length evens); Z.of_nat (length odds)]
  end.

Example test_case: solution [2; 2; 4; 6; 8; 7; 10; 2] = [2; 0].
Proof. reflexivity. Qed.