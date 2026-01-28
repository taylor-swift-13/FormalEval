Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition eat_spec (number : Z) (need : Z) (remaining : Z) (result : list Z) : Prop :=
  (0 <= number <= 1000) /\
  (0 <= need <= 1000) /\
  (0 <= remaining <= 1000) /\
  ((need <= remaining /\ result = [number + need; remaining - need]) \/
   (need > remaining /\ result = [number + remaining; 0])).

Example test_eat : eat_spec 499 501 700 [1000; 199].
Proof.
  unfold eat_spec.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * lia.
      * left.
        split.
        -- lia.
        -- simpl. reflexivity.
Qed.