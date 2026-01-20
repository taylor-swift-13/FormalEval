Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_left (fun acc y => if Z.eqb x y then acc + 1 else acc) l 0.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences l x) l in
  fold_left Z.max candidates (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 5%Z; 9%Z; 1%Z] = 2%Z.
Proof. reflexivity. Qed.