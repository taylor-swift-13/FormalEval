Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 2, output collisions = 4 *)
Example test_car_race_collision : car_race_collision_spec 2 4.
Proof.
  (* Unfold the definition of the specification *)
  unfold car_race_collision_spec.
  (* Simplify the arithmetic expression (2 * 2) *)
  simpl.
  (* Check for equality *)
  reflexivity.
Qed.