Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (l : list Z) (x : Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => (if Z.eq_dec h x then 1%nat else 0%nat) + count_occ t x
  end.

Fixpoint remove_duplicates (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if existsb (Z.eqb h) t then remove_duplicates t else h :: remove_duplicates t
  end.

Definition solution (l : list Z) : Z :=
  let distinct_elements := remove_duplicates l in
  let counts := map (count_occ l) distinct_elements in
  let duplicates := filter (fun c => Nat.ltb 1 c) counts in
  Z.of_nat (length duplicates).

Example test_case : solution [239; 39; 152; 39; 240; -339; -339] = 2.
Proof.
  compute.
  reflexivity.
Qed.