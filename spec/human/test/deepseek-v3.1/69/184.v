Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint count (z : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb z h then 1 else 0) + count z t
  end.

Fixpoint find_max_satisfying (lst : list Z) (candidates : list Z) (current_max : Z) : Z :=
  match candidates with
  | [] => current_max
  | h :: t =>
      if Z.of_nat (count h lst) >=? h then
        find_max_satisfying lst t (Z.max h current_max)
      else
        find_max_satisfying lst t current_max
  end.

Definition search_impl (lst : list Z) : Z :=
  match lst with
  | [] => (-1)%Z
  | _ =>
      let candidates := lst in
      let max_val := find_max_satisfying lst candidates (-1)%Z in
      if max_val =? (-1)%Z then
        (-1)%Z
      else
        max_val
  end.

Example test_case : search_impl 
  [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 9; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 5; 1; 3; 9] = 3.
Proof.
  unfold search_impl.
  simpl.
  (* count 1 in the list: 27 *)
  compute.
  (* count 2 in the list: 3 *)
  compute.
  (* count 3 in the list: 3 *)
  compute.
  (* count 4 in the list: 3 *)
  compute.
  (* count 5 in the list: 4 *)
  compute.
  (* count 6 in the list: 3 *)
  compute.
  (* count 7 in the list: 3 *)
  compute.
  (* count 8 in the list: 3 *)
  compute.
  (* count 9 in the list: 4 *)
  compute.
  (* count 10 in the list: 3 *)
  compute.
  (* Find max satisfying for each candidate:
        - 1: count 27 >= 1 → yes
        - 2: count 3 >= 2 → yes
        - 3: count 3 >= 3 → yes
        - 4: count 3 >= 4 → no
        - 5: count 4 >= 5 → no
        - 6: count 3 >= 6 → no
        - 7: count 3 >= 7 → no
        - 8: count 3 >= 8 → no
        - 9: count 4 >= 9 → no
        - 10: count 3 >= 10 → no
  *)
  reflexivity.
Qed.