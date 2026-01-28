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

Example test_eat : eat_spec 4 5 1 [5; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 4 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 5 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 1 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (5) > remaining (1), we take the right branch *)
        right.
        split.
        -- (* Prove 5 > 1 *)
           lia.
        -- (* Prove result equality [5; 0] = [4 + 1; 0] *)
           simpl.
           reflexivity.
Qed.