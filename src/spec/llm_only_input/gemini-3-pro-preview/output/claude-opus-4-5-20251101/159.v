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

Example test_eat_1: eat_spec 5 6 10 [11; 4].
Proof.
  unfold eat_spec.
  (* Use repeat split to separate conjunctions and try lia to solve range constraints *)
  repeat split; try lia.
  (* The remaining goal is the disjunction logic *)
  left.
  split.
  - (* Prove need <= remaining *)
    lia.
  - (* Prove result equality *)
    simpl. reflexivity.
Qed.