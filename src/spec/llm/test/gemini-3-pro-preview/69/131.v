Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occ x t
  end.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => 
    if count_occ x l >=? x then Z.max acc x else acc
  ) (-1) l.

Example search_example : search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 3%Z.
Proof. reflexivity. Qed.