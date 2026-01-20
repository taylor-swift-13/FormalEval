Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h n then 1 else 0) + count n t
  end.

Fixpoint search_iter (k : nat) (l : list Z) : Z :=
  match k with
  | O => -1
  | S k' =>
      let z := Z.of_nat k in
      if count z l >=? z then z else search_iter k' l
  end.

Definition search (l : list Z) : Z :=
  search_iter (length l) l.

Example test_search:
  search [20%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z] = 3%Z.
Proof.
  reflexivity.
Qed.