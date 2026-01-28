Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec y x then 1 + c else c) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occ l x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_case: search [9; 6; 5; 4; 3; 1; 1; 9] = 1.
Proof.
  vm_compute. reflexivity.
Qed.