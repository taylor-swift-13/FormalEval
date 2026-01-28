Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if count l x >=? x then Z.max acc x else acc) (-1) l.

Example search_example:
  search [1; 1; 1; 1; 3; 1; 2; 2; 2; 2; 1; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 13; 12; 13; 4; 7] = 4.
Proof.
  reflexivity.
Qed.