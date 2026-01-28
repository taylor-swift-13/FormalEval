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

Example test_case : search_impl [1;1;1;1;1;1;2;2;2;2;2;3;3;3;3;4;4;4;4;4;4;5;5;5;6;6;6;12;7;7;8;8;9;9;10;10;11;11;12;13] = 4.
Proof.
  unfold search_impl.
  simpl.
  
  (* First candidate: 1 *)
  simpl.
  compute.
  
  (* Second candidate: 1 *)
  simpl.
  compute.
  
  (* Third candidate: 1 *)
  simpl.
  compute.
  
  (* Fourth candidate: 1 *)
  simpl.
  compute.
  
  (* Fifth candidate: 1 *)
  simpl.
  compute.
  
  (* Sixth candidate: 1 *)
  simpl.
  compute.
  
  (* Seventh candidate: 2 *)
  simpl.
  compute.
  
  (* Eighth candidate: 2 *)
  simpl.
  compute.
  
  (* Ninth candidate: 2 *)
  simpl.
  compute.
  
  (* Tenth candidate: 2 *)
  simpl.
  compute.
  
  (* Eleventh candidate: 2 *)
  simpl.
  compute.
  
  (* Twelfth candidate: 3 *)
  simpl.
  compute.
  
  (* Thirteenth candidate: 3 *)
  simpl.
  compute.
  
  (* Fourteenth candidate: 3 *)
  simpl.
  compute.
  
  (* Fifteenth candidate: 3 *)
  simpl.
  compute.
  
  (* Sixteenth candidate: 4 *)
  simpl.
  compute.
  
  (* Seventeenth candidate: 4 *)
  simpl.
  compute.
  
  (* Eighteenth candidate: 4 *)
  simpl.
  compute.
  
  (* Nineteenth candidate: 4 *)
  simpl.
  compute.
  
  (* Twentieth candidate: 4 *)
  simpl.
  compute.
  
  (* Final check *)
  reflexivity.
Qed.