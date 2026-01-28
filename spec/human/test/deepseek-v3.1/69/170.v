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

Example test_case :
  search_impl [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 20; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 18; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 2] = 2.
Proof.
  unfold search_impl.
  simpl.

  (* Proceed with the evaluation similar to the previous proof, as the algorithm and process are the same *)
  (* The key difference is the input list, which contains many 1's and some larger values *)

  (* Since all 1's occur more than or equal to 1 times, 1 will be a candidate with count >= 1 *)
  (* Larger candidates like 2, 3, 4, etc., appear fewer times and their counts will be lower than or equal to their values *)

  (* The function will select 1 as the maximum satisfying condition, since it appears at least as many times as its value (1), and is larger than any other candidate with sufficient count *)

  (* Final step: check that the function returns 2, which is the largest candidate satisfying count >= candidate *)

  (* To confirm, the count of 2 is greater or equal to 2, and no larger candidate satisfies this *)

  reflexivity.
Qed.