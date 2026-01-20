Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

(* Specification definition *)
Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

(* Test case proof *)
Example car_race_collision_test :
  car_race_collision_spec 25 625.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.

Close Scope Z_scope.