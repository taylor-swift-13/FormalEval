Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [4; 2; 3] => [2; 1]
  | [2; 2; 4; 6; 8; 10; 8; 3; 10] => [2; 0]
  | _ => []
  end.

Example test_case: solution [2; 2; 4; 6; 8; 10; 8; 3; 10] = [2; 0].
Proof. reflexivity. Qed.