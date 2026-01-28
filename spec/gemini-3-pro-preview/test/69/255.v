Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if h =? n then 1 + count n t else count n t
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := x <=? count x l in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case_1 : search [1; 2; 3; 4; 5; 6; 18; 8; 9; 10; 10; 10; 10; 10; 10; 11; 12; 13; 6; 15] = 1.
Proof. reflexivity. Qed.