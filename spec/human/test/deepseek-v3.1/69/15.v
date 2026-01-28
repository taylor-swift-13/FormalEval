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

Example test_case : search_impl [2; 10; 4; 8; 2; 10; 5; 1; 2; 9; 5; 5; 6; 3; 8; 6; 4; 10] = 2.
Proof.
  unfold search_impl.
  simpl.
  (* First candidate: 2 *)
  simpl.
  compute.
  (* Second candidate: 10 *)
  simpl.
  compute.
  (* Third candidate: 4 *)
  simpl.
  compute.
  (* Fourth candidate: 8 *)
  simpl.
  compute.
  (* Fifth candidate: 2 *)
  simpl.
  compute.
  (* Sixth candidate: 10 *)
  simpl.
  compute.
  (* Seventh candidate: 5 *)
  simpl.
  compute.
  (* Eighth candidate: 1 *)
  simpl.
  compute.
  (* Ninth candidate: 2 *)
  simpl.
  compute.
  (* Tenth candidate: 9 *)
  simpl.
  compute.
  (* Eleventh candidate: 5 *)
  simpl.
  compute.
  (* Twelfth candidate: 5 *)
  simpl.
  compute.
  (* Thirteenth candidate: 6 *)
  simpl.
  compute.
  (* Fourteenth candidate: 3 *)
  simpl.
  compute.
  (* Fifteenth candidate: 8 *)
  simpl.
  compute.
  (* Sixteenth candidate: 6 *)
  simpl.
  compute.
  (* Seventeenth candidate: 4 *)
  simpl.
  compute.
  (* Eighteenth candidate: 10 *)
  simpl.
  compute.
  reflexivity.
Qed.