Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => sum t
  end.

Example test_case_1 : solution [1%Z; -29%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -10%Z] = -43%Z.
Proof. reflexivity. Qed.