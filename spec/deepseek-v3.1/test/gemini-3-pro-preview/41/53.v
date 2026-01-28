Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Specification definition *)
Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

(* Test case: input n = 9998, output collisions = 99960004 *)
Example car_race_collision_test : car_race_collision_spec 9998 99960004.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.