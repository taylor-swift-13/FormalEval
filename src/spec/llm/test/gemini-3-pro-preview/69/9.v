Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h n then S (count n t) else count n t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? Z.of_nat (count x l)) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [8; 8; 3; 6; 5; 6; 4] = -1.
Proof. reflexivity. Qed.