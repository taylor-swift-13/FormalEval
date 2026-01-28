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

Example test_eat : eat_spec 499 601 499 [998; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 499 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 601 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 499 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (601) > remaining (499), we take the right branch *)
        right.
        split.
        -- (* Prove 601 > 499 *)
           lia.
        -- (* Prove result equality [998; 0] = [499 + 499; 0] *)
           simpl.
           reflexivity.
Qed.