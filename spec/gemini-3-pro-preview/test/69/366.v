Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h n then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let p x := Z.leb x (count x l) in
  let candidates := filter p l in
  fold_left Z.max candidates (-1).

Example test_case: search [1; 2; 3; 4; 5; 6; 18; 8; 6; 10; 10; 10; 10; 10; 10; 11; 12; 13; 15; 1] = 1.
Proof. reflexivity. Qed.