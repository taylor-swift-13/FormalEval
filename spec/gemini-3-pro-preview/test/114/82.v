Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      match xs with
      | [] => x
      | _ => Z.min x (min_element xs)
      end
  end.

Example test_min_element: min_element [-6%Z; 6%Z; 5%Z; 3%Z; -2%Z; -3%Z; 0%Z; 4%Z; 3%Z; -8%Z] = -8%Z.
Proof. reflexivity. Qed.