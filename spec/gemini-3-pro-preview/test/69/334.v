Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let fix count_occ (x : Z) (lst : list Z) : Z :=
    match lst with
    | [] => 0
    | h :: t => (if Z.eqb h x then 1 else 0) + count_occ x t
    end in
  let valid (x : Z) := Z.geb (count_occ x l) x in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 9%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 2%Z; 10%Z; 10%Z; 1%Z; 1%Z] = 3%Z.
Proof. reflexivity. Qed.