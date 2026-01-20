Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
    let min_val := fold_right Z.min x xs in
    let count := fold_right (fun y c => if Z.eqb y min_val then c + 1 else c) 0 l in
    min_val * count
  end.

Example test_case : solution [1; -2; 3; -4; -1; 5; -6; 7; -8; 9; -10; -10] = -20.
Proof. reflexivity. Qed.