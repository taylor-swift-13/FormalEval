Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_list xs)
  end.

Fixpoint count_neg (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if x <? 0 then 1 else 0) + count_neg xs
  end.

Definition solution (l : list Z) : Z :=
  min_list l - count_neg l.

Example test_case: solution [2%Z; 1%Z; 2%Z; -3%Z; -1%Z; 1%Z; -5%Z; 5%Z; 5%Z] = -8%Z.
Proof.
  reflexivity.
Qed.