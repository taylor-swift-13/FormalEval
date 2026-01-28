Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (n : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eqb h n then 1 + count_occurrences t n else count_occurrences t n
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun n => Z.geb (count_occurrences l n) n) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.max h t
  end.

Example test_search : search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 4%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 4%Z.
Proof. reflexivity. Qed.