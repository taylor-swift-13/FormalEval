Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h n then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let p x := x <=? count x l in
  let candidates := filter p l in
  fold_left Z.max candidates (-1).

Example test_case: search [5; 5; 5; 4; 3; 5; 4] = -1.
Proof. reflexivity. Qed.