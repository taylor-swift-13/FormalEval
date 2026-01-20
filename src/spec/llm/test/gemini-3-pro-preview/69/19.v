Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x target then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_left Z.max candidates (-1).

Example test_search: search [9%Z; 8%Z; 6%Z; 10%Z; 2%Z; 6%Z; 10%Z; 2%Z; 7%Z; 8%Z; 10%Z; 3%Z; 8%Z; 2%Z; 6%Z; 2%Z; 3%Z; 1%Z] = 2%Z.
Proof.
  reflexivity.
Qed.