Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Specification definition *)
Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

(* Test case: input n = 987654, output collisions = 975460423716 *)
Example car_race_collision_test : car_race_collision_spec 987654 975460423716.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.