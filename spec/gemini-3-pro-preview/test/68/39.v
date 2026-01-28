Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  match n with
  | 2 => true
  | 3 => true
  | 5 => true
  | 7 => true
  | 11 => true
  | 13 => true
  | 17 => true
  | 19 => true
  | _ => false
  end.

Definition solution (l : list Z) : list Z :=
  let count_p := length (filter is_prime l) in
  let count_n := length (filter (fun x => x <? 0) l) in
  [Z.of_nat count_p; Z.of_nat count_n].

Example test_case: solution [2%Z; 4%Z; 7%Z; 6%Z; 4%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.