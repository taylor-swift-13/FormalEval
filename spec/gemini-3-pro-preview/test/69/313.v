Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eqb y x then c + 1 else c) 0 lst.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences lst x) lst in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 17%Z; 3%Z; 3%Z; 19%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 19%Z] = 4%Z.
Proof.
  compute. reflexivity.
Qed.