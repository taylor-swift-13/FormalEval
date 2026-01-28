Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (n : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eq_dec h n then 1 + count_occurrences t n else count_occurrences t n
  end.

Definition search (l : list Z) : Z :=
  fold_left Z.max (filter (fun x => x <=? count_occurrences l x) l) (-1).

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 5%Z; 1%Z] = 2%Z.
Proof. reflexivity. Qed.