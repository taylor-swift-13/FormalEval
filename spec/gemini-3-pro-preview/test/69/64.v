Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h n then 1 else 0) + count_occ n t
  end.

Definition search (l : list Z) : Z :=
  let p x := x <=? count_occ x l in
  let filtered := filter p l in
  fold_left Z.max filtered (-1).

Example test_search : search [2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 10%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z] = 2%Z.
Proof. reflexivity. Qed.