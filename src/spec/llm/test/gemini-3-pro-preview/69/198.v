Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if n =? x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count l x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 18; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 7; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10]%Z = 2%Z.
Proof.
  compute. reflexivity.
Qed.