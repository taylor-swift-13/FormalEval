Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y acc => if Z.eq_dec x y then acc + 1 else acc) 0 l in
  let filtered := filter (fun x => x <=? count x) l in
  fold_right Z.max (-1) filtered.

Example test_case: search [3; 2; 1; 1; 1; 1; 1; 1] = 1.
Proof. reflexivity. Qed.