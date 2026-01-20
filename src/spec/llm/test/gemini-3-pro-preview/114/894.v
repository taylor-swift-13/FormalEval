Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : nat :=
  length (filter (Z.eqb x) l).

Definition solve (l : list Z) : Z :=
  let uniques := filter (fun x => Nat.eqb (count l x) 1) l in
  match uniques with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Example test_case: solve [1; -1; 1; 1; -1; 1; -20; 1; -1; 21; 1; -1; 1; -1] = -20.
Proof. reflexivity. Qed.