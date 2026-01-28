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

Example test_case : search_impl [1; 2; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 4; 4; 4] = 4.
Proof.
  unfold search_impl.
  simpl.
  (* For each candidate, compute counts and verify conditions *)
  (* counts:
     1: 3
     2: 4
     3: 2
     4: 6
  *)
  (* Candidate 1: count 3 >= 1? Yes, max so far = 1 *)
  (* Candidate 2: count 4 >= 2? Yes, max so far = 2 *)
  (* Candidate 1: count 3 >= 1? Yes, max so far = 2 *)
  (* Candidate 1: count 3 >= 1? Yes, max so far = 2 *)
  (* Candidate 2: count 4 >= 2? Yes, max so far = 2 *)
  (* Candidate 2: count 4 >= 2? Yes, max so far = 2 *)
  (* Candidate 2: count 4 >= 2? Yes, max so far = 2 *)
  (* Candidate 3: count 2 >= 3? No *)
  (* Candidate 4: count 6 >= 4? Yes, max so far = 4 *)
  (* Candidate 3: count 2 >= 3? No *)
  (* Candidate 4: count 6 >= 4? Yes, max so far = 4 *)
  (* Candidate 4: count 6 >= 4? Yes, max so far = 4 *)
  (* Candidate 4: count 6 >= 4? Yes, max so far = 4 *)
  (* Candidate 4: count 6 >= 4? Yes, max so far = 4 *)
  (* Final max = 4 *)
  reflexivity.
Qed.