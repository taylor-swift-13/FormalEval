Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter (fun x => x mod 3 =? 0) l))].

Example test_case: solution [21; 2; 5; 7; 20; 5] = [2; 1].
Proof.
  reflexivity.
Qed.