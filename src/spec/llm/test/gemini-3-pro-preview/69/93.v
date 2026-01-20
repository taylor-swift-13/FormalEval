Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eqb n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_right Z.max (-1) (filter (fun x => Z.leb x (count_occ l x)) l).

Example test_search: search [10; 2; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 4; 4; 4] = 4.
Proof.
  vm_compute.
  reflexivity.
Qed.