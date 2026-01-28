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

Example test_eat : eat_spec 4 10 4 [8; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 4 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 10 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 4 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (10) > remaining (4), we take the right branch *)
        right.
        split.
        -- (* Prove 10 > 4 *)
           lia.
        -- (* Prove result equality [8; 0] = [4 + 4; 0] *)
           simpl.
           reflexivity.
Qed.