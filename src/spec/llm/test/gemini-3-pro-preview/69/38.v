Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if n =? h then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let valid x := x <=? count x l in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case: search [4; 5; 6; 4; 5; 3; 5; 5] = -1.
Proof. reflexivity. Qed.