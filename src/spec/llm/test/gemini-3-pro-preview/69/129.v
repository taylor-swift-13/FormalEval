Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_left (fun acc y => if Z.eq_dec y x then acc + 1 else acc) l 0.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => (x >? 0) && (count x l >=? x)) l in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3] = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.