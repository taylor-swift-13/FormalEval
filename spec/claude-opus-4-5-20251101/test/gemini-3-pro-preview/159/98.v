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

Example test_eat : eat_spec 2 3 1 [3; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 2 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 3 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 1 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (3) > remaining (1), we take the right branch *)
        right.
        split.
        -- (* Prove 3 > 1 *)
           lia.
        -- (* Prove result equality [3; 0] = [2 + 1; 0] *)
           simpl.
           reflexivity.
Qed.