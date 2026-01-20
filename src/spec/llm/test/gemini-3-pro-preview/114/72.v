Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => (if Z.eqb h x then 1%nat else 0%nat) + count x t
  end.

Definition solution (l : list Z) : Z :=
  let uniques := filter (fun x => Nat.eqb (count x l) 1) l in
  match uniques with
  | [] => 0
  | h :: t => fold_left Z.min t h
  end.

Example test_case: solution [3%Z; 2%Z; -5%Z; 4%Z; 2%Z; -3%Z; 2%Z; 5%Z; 4%Z] = -5%Z.
Proof. reflexivity. Qed.