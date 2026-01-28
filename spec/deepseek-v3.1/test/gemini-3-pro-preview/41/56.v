Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Specification definition *)
Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

(* Test case: input n = 9997, output collisions = 99940009 *)
Example car_race_collision_test : car_race_collision_spec 9997 99940009.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.