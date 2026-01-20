Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec y x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count_occurrences l x) x) l in
  fold_right Z.max (-1) candidates.

Example search_example: search [8; 8; 10; 6; 4; 3; 5; 8; 2; 4; 2; 8; 4; 6; 10; 4; 2; 1; 10; 2; 1; 1; 5] = 4.
Proof.
  reflexivity.
Qed.