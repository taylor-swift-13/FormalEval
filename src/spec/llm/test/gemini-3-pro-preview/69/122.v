Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 lst in
  let candidates := filter (fun x => count x >=? x) lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [3%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] = 1%Z.
Proof. reflexivity. Qed.