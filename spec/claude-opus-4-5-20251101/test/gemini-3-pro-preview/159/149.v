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

Example test_eat : eat_spec 700 800 600 [1300; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 700 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 800 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 600 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (800) > remaining (600), we take the right branch *)
        right.
        split.
        -- (* Prove 800 > 600 *)
           lia.
        -- (* Prove result equality [1300; 0] = [700 + 600; 0] *)
           simpl.
           reflexivity.
Qed.