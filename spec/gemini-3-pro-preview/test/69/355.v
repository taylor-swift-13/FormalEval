Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eq_dec x y then 1 else 0) + count_occ x tl
  end.

Definition search (l : list Z) : Z :=
  let candidates := nodup Z.eq_dec l in
  fold_left (fun acc x => if x <=? count_occ x l then Z.max acc x else acc) candidates (-1).

Example test_search:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 1%Z] = 3%Z.
Proof. reflexivity. Qed.