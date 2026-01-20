Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (n : Z) (l : list Z) : nat :=
  length (filter (Z.eqb n) l).

Definition solution (l : list Z) : Z :=
  let uniques := filter (fun n => Nat.eqb (count n l) 1) l in
  match uniques with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Example test_case: solution [1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -20%Z; 1%Z; -1%Z; 21%Z; 10%Z; -1%Z; 1%Z; -1%Z] = -20%Z.
Proof. reflexivity. Qed.