Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb n h then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let valid n := Z.geb (count n l) n in
  let candidates := filter valid l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_case: search [1; -1; 1; 1; -1; 1; -1; 1; -1; 1; -1] = -1.
Proof. reflexivity. Qed.