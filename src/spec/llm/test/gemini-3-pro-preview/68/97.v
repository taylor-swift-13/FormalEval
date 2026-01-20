Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_index (target : Z) (l : list Z) (idx : Z) : option Z :=
  match l with
  | [] => None
  | x :: xs => if Z.eqb x target then Some idx else find_index target xs (idx + 1)
  end.

Definition min_even (l : list Z) : option Z :=
  let evens := filter Z.even l in
  match evens with
  | [] => None
  | h :: t => Some (fold_right Z.min h t)
  end.

Definition solve (l : list Z) : list Z :=
  match min_even l with
  | None => []
  | Some val => 
      match find_index val l 0 with
      | None => []
      | Some idx => [val; idx]
      end
  end.

Example test_case: solve [12%Z; 21%Z; 13%Z; 8%Z; 13%Z; 7%Z] = [8%Z; 3%Z].
Proof. reflexivity. Qed.