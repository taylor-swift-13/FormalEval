Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eqb h n then S (count n t) else count n t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.leb x (Z.of_nat (count x l))) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_case : search [20%Z; -8%Z; -10%Z; 20%Z; -30%Z; 40%Z; -50%Z; 60%Z; 80%Z; -70%Z; 80%Z; -90%Z; 100%Z; 80%Z; 20%Z; -50%Z] = -90%Z.
Proof.
  reflexivity.
Qed.