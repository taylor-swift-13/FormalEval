Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eqb x h then 1 + count_occ x t else count_occ x t
  end.

Definition search (l : list Z) : Z :=
  let p x := Z.leb x (count_occ x l) in
  let candidates := filter p l in
  fold_left Z.max candidates (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 4%Z; 4%Z; 3%Z; 4%Z; 4%Z; 4%Z; 3%Z; 3%Z] = 4%Z.
Proof. reflexivity. Qed.