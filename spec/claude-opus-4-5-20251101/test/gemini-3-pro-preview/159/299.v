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

Example test_eat : eat_spec 250 599 801 [849; 202].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 250 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 599 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 801 <= 1000 *)
        lia.
      * (* Since need (599) <= remaining (801), we take the left branch *)
        left.
        split.
        -- (* Prove 599 <= 801 *)
           lia.
        -- (* Prove result equality *)
           simpl.
           reflexivity.
Qed.