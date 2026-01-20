Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if x =? y then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x =? count_occurrences l x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 1; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 2] = 3.
Proof.
  vm_compute. reflexivity.
Qed.