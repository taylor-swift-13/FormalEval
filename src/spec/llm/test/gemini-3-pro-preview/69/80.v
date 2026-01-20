Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb n h then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let p x := count x l >=? x in
  let candidates := filter p l in
  fold_right Z.max (-1) candidates.

Example test_search: search [3%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 1%Z; 6%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 1%Z; 3%Z] = 4%Z.
Proof. reflexivity. Qed.