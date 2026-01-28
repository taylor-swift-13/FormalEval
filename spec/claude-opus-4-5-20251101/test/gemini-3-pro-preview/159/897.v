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

Example test_eat : eat_spec 199 750 496 [695; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 199 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 750 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 496 <= 1000 *)
        lia.
      * (* Since need (750) > remaining (496), we take the right branch *)
        right.
        split.
        -- (* Prove 750 > 496 *)
           lia.
        -- (* Prove result equality [695; 0] = [199 + 496; 0] *)
           simpl.
           reflexivity.
Qed.