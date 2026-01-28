Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_elements_at_odd_indices (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => if Nat.odd i then x :: get_elements_at_odd_indices xs (S i)
               else get_elements_at_odd_indices xs (S i)
  end.

Definition solution (l : list Z) : list Z :=
  let odds := get_elements_at_odd_indices l 0 in
  let evens := filter Z.even odds in
  [fold_right Z.add 0 evens; Z.of_nat (length evens)].

Example test_case: solution [7%Z; 6%Z; 7%Z; 1%Z] = [6%Z; 1%Z].
Proof. reflexivity. Qed.