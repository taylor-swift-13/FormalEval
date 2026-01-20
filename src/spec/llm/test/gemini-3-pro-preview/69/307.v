Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eqb x target then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 10%Z; 10%Z; 5%Z; 6%Z; 11%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 8%Z; 8%Z; 9%Z; 10%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z] = 1%Z.
Proof. compute. reflexivity. Qed.