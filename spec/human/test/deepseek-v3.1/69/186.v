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

Example test_case : search_impl [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 10; 5; 6; 7; 8; 9; 10] = 5.
Proof.
  unfold search_impl.
  simpl.

  (* Count of 5 in the list is 4 *)
  compute.

  (* Count of 6 is 4 *)
  compute.

  (* Count of 7 is 4 *)
  compute.

  (* Count of 8 is 4 *)
  compute.

  (* Count of 9 is 4 *)
  compute.

  (* Count of 10 is 4 *)
  compute.

  (* For numbers 1, 2, 3, counts are 1 each, which is less than the number itself *)
  (* So, they don't satisfy the condition *)
  
  (* Final max satisfying number is 5 *)
  reflexivity.
Qed.