Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Specification definition *)
Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

(* Test case: input n = 100000, output collisions = 10000000000 *)
Example car_race_collision_test : car_race_collision_spec 100000 10000000000.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.