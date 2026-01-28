Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eqb n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => (x >? 0) && (count l x >=? x)) l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15] = 1.
Proof. reflexivity. Qed.