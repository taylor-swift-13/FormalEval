Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eqb x y then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.leb x (count_occurrences l x)) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 2%Z; 10%Z; 4%Z; 5%Z; 6%Z; 7%Z; 4%Z; 10%Z; 7%Z; 7%Z; 6%Z] = 1%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.