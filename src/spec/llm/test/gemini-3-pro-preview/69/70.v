Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eq_dec y x then c + 1 else c) 0 l in
  let candidates := filter (fun x => x <=? count x) l in
  fold_right Z.max (-1) candidates.

Example search_example : search [5; 5; 4; 5; 5; 5] = 5.
Proof. reflexivity. Qed.