Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occurrences l x >=? x) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.max h t
  end.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 18; 2; 2; 18; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 7; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 1] = 3.
Proof.
  compute. reflexivity.
Qed.