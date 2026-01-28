Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 l in
  let candidates := filter (fun x => x <=? count x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [9%Z; 6%Z; 5%Z; 5%Z; 4%Z; 3%Z; 1%Z; 1%Z] = 1%Z.
Proof. reflexivity. Qed.