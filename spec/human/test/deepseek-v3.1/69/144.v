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

Example test_case : search_impl [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 20; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 18; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10] = 2.
Proof.
  unfold search_impl.
  simpl.
  
  (* Initial candidates: [1; 1; ...; 10] with various repetitions *)
  (* The function will check counts for each candidate *)
  
  (* Since all 1's appear many times, count 1 [ ... ] >= 1, so 1 is a candidate *)
  (* For candidates like 2, count 2 ... the number of 2's in the list *)
  (* count 2 in the list is 3, which is >= 2, so 2 is also a candidate *)
  
  (* For larger numbers like 20, count(20, list) = 1, which is >=20? No. So discarded *)
  
  (* For 18, count 18 = 1, which is >= 18? No. Discard *)
  
  (* For 3, count 3 = 2, which is >= 3? No. Discard *)
  
  (* For 4, count 4=3, !=4, discard *)
  
  (* For 5, count=3, discard *)
  
  (* For 6, count=3, discard *)
  
  (* For 7, count=3, discard *)
  
  (* For 8, count=3, discard *)
  
  (* For 9, count=3, discard *)
  
  (* For 10, count=3, discard *)
  
  (* The maximum candidate satisfying the condition: 2, since count 2=3 >= 2 and no larger candidate meets the condition *)
  
  (* Now, find the maximum satisfying candidate: 2 *)
  (* The function should select 2 *)
  
  (* The final output is 2 *)
  
  reflexivity.
Qed.