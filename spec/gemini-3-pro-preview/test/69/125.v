Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec y x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => (x >? 0) && (count_occurrences l x >=? x)) l in
  fold_right Z.max (-1) filtered.

Example test_case: search [1; 1; 1; 6; 5; 2; 3; 3] = 1.
Proof.
  compute. reflexivity.
Qed.