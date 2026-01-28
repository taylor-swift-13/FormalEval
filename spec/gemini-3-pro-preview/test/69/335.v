Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eqb x target then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let p x := Z.leb x (count x l) in
  let candidates := filter p l in
  fold_right Z.max (-1) candidates.

Example search_example: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 10%Z; 2%Z; 2%Z; 3%Z; 11%Z; 3%Z; 17%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 12%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z] = 4%Z.
Proof. reflexivity. Qed.