Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb n h then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.leb x (count x l)) l in
  fold_left Z.max candidates (-1).

Example test_search : search [3; 2; 1; 1; 1; 1; 1] = 1.
Proof. reflexivity. Qed.