Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

Example test_car_race_collision : car_race_collision_spec 2 4.
Proof.
  (* Unfold the specification definition *)
  unfold car_race_collision_spec.
  
  (* Simplify the arithmetic expression (2 * 2) *)
  simpl.
  
  (* Verify that 4 equals 4 *)
  reflexivity.
Qed.