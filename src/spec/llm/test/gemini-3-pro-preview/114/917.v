Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.

Fixpoint solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => 
      match xs with
      | [] => x
      | _ => Z.min x (solution xs)
      end
  end.

Example test_case: solution [1; 1; 1; -1; 1; -20; 1; -1; 21; 1; -1; 1; -1] = -20.
Proof. reflexivity. Qed.