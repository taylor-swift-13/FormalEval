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

Example test_eat : eat_spec 201 800 602 [803; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 201 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 800 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 602 <= 1000 *)
        lia.
      * (* Since need (800) > remaining (602), we take the right branch *)
        right.
        split.
        -- (* Prove 800 > 602 *)
           lia.
        -- (* Prove result equality [803; 0] = [201 + 602; 0] *)
           simpl.
           reflexivity.
Qed.