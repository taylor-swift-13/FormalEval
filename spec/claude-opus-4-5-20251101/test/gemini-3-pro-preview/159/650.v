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

Example test_eat : eat_spec 251 300 199 [450; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 251 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 300 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 199 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (300) > remaining (199), we take the right branch *)
        right.
        split.
        -- (* Prove 300 > 199 *)
           lia.
        -- (* Prove result equality [450; 0] = [251 + 199; 0] *)
           simpl.
           reflexivity.
Qed.