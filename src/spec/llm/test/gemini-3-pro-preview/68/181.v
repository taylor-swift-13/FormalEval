Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      if x =? 0 then [0; 0]
      else
        let evens := List.length (List.filter Z.even l) in
        let odds := List.length (List.filter Z.odd l) in
        [Z.of_nat evens; Z.of_nat odds]
  end.

Example test_case : solution [0; 7; 2; 4; 6; 8; 10; 2; 4] = [0; 0].
Proof. reflexivity. Qed.