Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

Definition eat_spec (number : Z) (need : Z) (remaining : Z) (result : list Z) : Prop :=
  (0 <= number <= 1000) /\
  (0 <= need <= 1000) /\
  (0 <= remaining <= 1000) /\
  ((need <= remaining /\ result = [number + need; remaining - need]) \/
   (need > remaining /\ result = [number + remaining; 0])).

Example eat_test_2 : eat_spec 198 0 996 [198; 996].
Proof.
  unfold eat_spec.
  repeat split; try lia.
  left.
  split.
  - lia.
  - reflexivity.
Qed.