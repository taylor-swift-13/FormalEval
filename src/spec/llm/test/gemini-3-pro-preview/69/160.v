Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (n : Z) (l : list Z) : Z :=
  fold_left (fun acc x => if Z.eqb x n then acc + 1 else acc) l 0.

Definition search (l : list Z) : Z :=
  let p x := (x >? 0) && (count x l >=? x) in
  let valid := filter p l in
  fold_left Z.max valid (-1).

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 11%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 12%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z] = 4%Z.
Proof.
  vm_compute. reflexivity.
Qed.