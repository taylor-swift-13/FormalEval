Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n c => if n =? x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if count l x >=? x then Z.max acc x else acc) (-1) l.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 14%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 2%Z] = 3%Z.
Proof.
  reflexivity.
Qed.