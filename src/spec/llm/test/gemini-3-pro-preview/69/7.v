Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.leb x (count_occurrences l x)) l in
  fold_right Z.max (-1) candidates.

Example example_test_case: search [3; 2; 8; 2] = 2.
Proof.
  compute. reflexivity.
Qed.