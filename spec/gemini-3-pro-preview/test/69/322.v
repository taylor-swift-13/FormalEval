Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if y =? x then c + 1 else c) 0 l in
  let valid (x : Z) := x <=? count x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 13%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 12%Z; 7%Z; 8%Z; 9%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 21%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.