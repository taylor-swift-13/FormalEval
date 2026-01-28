Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : nat :=
  length (filter (Z.eqb x) l).

Definition solution (l : list Z) : Z :=
  let unique := filter (fun x => Nat.eqb (count x l) 1) l in
  match unique with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Example test_case: solution [1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 49%Z; -20%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -20%Z.
Proof.
  unfold solution.
  simpl.
  reflexivity.
Qed.