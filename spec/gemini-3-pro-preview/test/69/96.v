Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n c => if Z.eq_dec n x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (x >? 0) && (count l x >=? x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [5; 5; 3; 4; 3; 5; 5; 5; 3] = 5.
Proof.
  compute. reflexivity.
Qed.