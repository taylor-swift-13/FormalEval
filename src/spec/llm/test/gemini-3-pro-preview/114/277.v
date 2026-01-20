Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint insert (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if x <? h then x :: l else h :: insert x t
  end.

Fixpoint sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 (firstn 3 (sort l)).

Example test_case: solution [-3; -2; 3; -4; 5; 50; 7; -8; -50000; -10; 50; 7] = -50018.
Proof. reflexivity. Qed.