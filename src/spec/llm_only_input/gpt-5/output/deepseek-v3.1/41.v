Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = (n * n)%nat.

Example car_race_collision_spec_2 : car_race_collision_spec 2%nat 4%nat.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Definition car_race_collision_from_input (input : list Z) : option Z :=
  match input with
  | [n] => Some (n * n)
  | _ => None
  end.

Example car_race_collision_test_input_output :
  car_race_collision_from_input [2%Z] = Some 4%Z.
Proof.
  simpl.
  reflexivity.
Qed.