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
  let valid := filter (fun x => x <=? Z.of_nat (count x l)) l in
  fold_right Z.max (-1) valid.

Example test_search: search [1; 2; 3; 4; 5; 6; 7; 8; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15] = 1.
Proof.
  reflexivity.
Qed.