Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb x h then 1 else 0) + count x t
  end.

Fixpoint filter_even (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.even h then h :: filter_even t else filter_even t
  end.

Fixpoint min_list (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
      match min_list t with
      | None => Some h
      | Some m => Some (Z.min h m)
      end
  end.

Definition solution (l : list Z) : list Z :=
  match min_list (filter_even l) with
  | None => []
  | Some m => [m; count m l]
  end.

Example test_case: solution [1; 1; 1; 1; 1; 2; 2; 27; 2; 2; 2] = [2; 5].
Proof. reflexivity. Qed.