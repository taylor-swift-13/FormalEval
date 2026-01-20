Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if n =? h then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 2; 4; 4; 4; 4; 4] = 4.
Proof.
  compute.
  reflexivity.
Qed.