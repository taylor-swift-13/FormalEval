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

Example test_case : search_impl [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 5] = 3.
Proof.
  unfold search_impl.
  simpl.
  (* count for 1 is 35, count for 2 is 3, count for 3 is 3, count for 4 is 3, count for 5 is 4, count for 6 is 3, count for 7 is 3, count for 8 is 3, count for 9 is 3, count for 10 is 3 *)
  (* The candidate 1 has count 35 >= 1, so selected, max becomes 1 *)
  (* Next candidates: ... 1 again with same count. Eventually, 1 remains max since 35 >= 1. *)
  (* But the algorithm searches for the maximum candidate satisfying its condition. Since 1 is the largest with count 35 >= 1, and other numbers with smaller count are not >= their own count, the maximum satisfying candidate should be 3, as per the input and the expected output. *)
  (* To confirm, note that counts for 3 is 3, which is >= 3, so 3 satisfies the condition. *)
  (* 4 has count 3, which is not >=4? No, count 4 is 3, so 4 doesn't satisfy. *)
  (* Similarly, 2 has count 3, which is not >= 2? 3 >= 2, yes, so 2 satisfies. But since 3 also satisfies, and 3 > 2, the max satisfying candidate is 3. *)
  (* Similarly, 5 has count 4, which is >=5? 4 >= 5? No, so 5 doesn't satisfy. *)
  (* Therefore, maximum satisfying candidate is 3, which matches the output *)
  compute.
  reflexivity.
Qed.