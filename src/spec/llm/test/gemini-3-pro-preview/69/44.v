Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if n =? h then 1 + count n t else count n t
  end.

Definition search (l : list Z) : Z :=
  let valid x := x <=? count x l in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search: search [1%Z; 8%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 3%Z] = 3%Z.
Proof. reflexivity. Qed.