Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y acc => if Z.eq_dec x y then acc + 1 else acc) 0 l in
  let candidates := filter (fun x => Z.geb (count x) x) l in
  fold_right Z.max (-1) candidates.

Example test_search : search [1%Z; 6%Z; 10%Z; 1%Z; 6%Z; 9%Z; 10%Z; 8%Z; 6%Z; 8%Z; 7%Z; 3%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.