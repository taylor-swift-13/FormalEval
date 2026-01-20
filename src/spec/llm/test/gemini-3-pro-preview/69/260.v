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
  let valid x := Z.leb x (count x l) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 2%Z; 3%Z; 17%Z; 5%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 10%Z] = 1%Z.
Proof. reflexivity. Qed.