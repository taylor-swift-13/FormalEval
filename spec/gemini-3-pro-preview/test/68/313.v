Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | x :: y :: _ => [x / 2; y / 2]
  | _ => []
  end.

Example test_case : solution [0; 1; 2; 5; 3; 7; 9; 10; 7; 10] = [0; 0].
Proof. reflexivity. Qed.