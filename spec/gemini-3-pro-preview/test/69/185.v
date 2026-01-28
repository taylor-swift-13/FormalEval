Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if target =? x then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let p x := (0 <? x) && (x <=? count x l) in
  let candidates := filter p l in
  fold_left Z.max candidates (-1).

Example test_case : search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 1%Z; 14%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 1%Z] = 3%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.