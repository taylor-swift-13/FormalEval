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

Example test_case : search_impl [2; 2; 4; 4; 4; 4; 4; 4; 2; 4] = 4.
Proof.
  unfold search_impl.
  simpl.
  (* First candidate: 2 *)
  simpl.
  compute. (* count 2 [2; 2; 4; 4; 4; 4; 4; 4; 2; 4] *)
  (* count 2 = 3 *)
  (* Check if 3 >= 2 *)
  (* Yes, so candidate 2 is valid, but continue to see if larger satisfying candidate exists *)
  (* Next candidate: 2 (again) *)
  simpl.
  compute.
  (* count 4 [2; 2; 4; 4; 4; 4; 4; 4; 2; 4] *)
  (* count 4 = 6 *)
  (* Check if 6 >= 4 *)
  (* Yes, so 4 is candidate *)
  (* Next candidate: 4 (multiple times) *)
  simpl.
  compute.
  (* count 4 again *)
  (* count 4 = 6 *)
  (* 6 >= 4, continue *)
  simpl.
  compute.
  (* count 4 again at the last position *)
  (* 6 >= 4, candidate remains 4 *)
  (* Next candidate: 4 *)
  simpl.
  compute.
  (* Confirming candidate 4 remains valid *)
  reflexivity.
Qed.