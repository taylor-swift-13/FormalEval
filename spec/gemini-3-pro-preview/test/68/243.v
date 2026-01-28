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

Fixpoint count_odds (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.odd h then 1 else 0) + count_odds t
  end.

Fixpoint sum_even_indices_aux (l : list Z) (idx : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.even h then idx else 0) + sum_even_indices_aux t (idx + 1)
  end.

Definition solution (l : list Z) : list Z :=
  [sum_even_indices_aux (sort l) 0; count_odds l].

Example test_case: solution [1%Z; 3%Z; 8%Z; 7%Z; 6%Z; 9%Z] = [6%Z; 4%Z].
Proof. reflexivity. Qed.