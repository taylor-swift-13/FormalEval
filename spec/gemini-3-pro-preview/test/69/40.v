Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h n then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let fix aux (n : nat) : Z :=
    match n with
    | O => -1
    | S n' => 
      let z := Z.of_nat n in
      if z <=? count z l then z else aux n'
    end
  in aux (length l).

Example test_search: search [4%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z] = 2%Z.
Proof. reflexivity. Qed.