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

Example test_case : search_impl [2; 6; 4; 2; 8; 7; 5; 6; 4; 10; 4; 6; 3; 7; 8; 8; 3; 1; 4; 2; 2; 10; 7] = 4.
Proof.
  unfold search_impl.
  simpl.

  (* First candidate: 2 *)
  simpl.
  compute.

  (* Second candidate: 6 *)
  simpl.
  compute.

  (* Third candidate: 4 *)
  simpl.
  compute.

  (* Fourth candidate: 2 *)
  simpl.
  compute.

  (* Fifth candidate: 8 *)
  simpl.
  compute.

  (* Sixth candidate: 7 *)
  simpl.
  compute.

  (* Seventh candidate: 5 *)
  simpl.
  compute.

  (* Eighth candidate: 6 *)
  simpl.
  compute.

  (* Ninth candidate: 4 *)
  simpl.
  compute.

  (* Tenth candidate: 10 *)
  simpl.
  compute.

  (* Eleventh candidate: 4 *)
  simpl.
  compute.

  (* Twelfth candidate: 6 *)
  simpl.
  compute.

  (* Thirteenth candidate: 3 *)
  simpl.
  compute.

  (* Fourteenth candidate: 7 *)
  simpl.
  compute.

  (* Fifteenth candidate: 8 *)
  simpl.
  compute.

  (* Sixteenth candidate: 8 *)
  simpl.
  compute.

  (* Seventeenth candidate: 3 *)
  simpl.
  compute.

  (* Eighteenth candidate: 1 *)
  simpl.
  compute.

  (* Nineteenth candidate: 4 *)
  simpl.
  compute.

  (* Twentieth candidate: 2 *)
  simpl.
  compute.

  (* Twenty-first candidate: 2 *)
  simpl.
  compute.

  (* Twenty-second candidate: 10 *)
  simpl.
  compute.

  (* Twenty-third candidate: 7 *)
  simpl.
  compute.

  (* Final check *)
  reflexivity.
Qed.