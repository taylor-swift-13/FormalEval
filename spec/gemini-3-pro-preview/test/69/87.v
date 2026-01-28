Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if y =? x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occ l x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 2%Z; 2%Z; 2%Z; 2%Z] = 2%Z.
Proof.
  reflexivity.
Qed.