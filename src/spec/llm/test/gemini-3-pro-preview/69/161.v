Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_left (fun acc y => if Z.eqb y x then acc + 1 else acc) l 0.

Definition search (l : list Z) : Z :=
  let valid x := (x >? 0) && (count_occ l x >=? x) in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search: search (
  (repeat 1 35%nat) ++
  (repeat 2 3%nat) ++
  (repeat 18 1%nat) ++
  (repeat 3 3%nat) ++
  (repeat 4 2%nat) ++
  (repeat 5 3%nat) ++
  (repeat 6 2%nat) ++
  (repeat 7 4%nat) ++
  (repeat 8 3%nat) ++
  (repeat 9 3%nat) ++
  (repeat 10 3%nat)
) = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.