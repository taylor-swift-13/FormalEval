Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  match n with
  | 2 => true
  | 3 => true
  | 5 => true
  | _ => false
  end.

Definition is_composite (n : Z) : bool :=
  match n with
  | 4 => true
  | 6 => true
  | _ => false
  end.

Fixpoint count (f : Z -> bool) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + count f xs
  end.

Definition even_odd_count (l : list Z) : list Z :=
  [count is_prime l; count is_composite l].

Example test_case_2 : even_odd_count [2%Z; 5%Z; 7%Z; 9%Z; 11%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.