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

Example test_eat : eat_spec 502 249 250 [751; 1].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 502 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 249 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 250 <= 1000 *)
        lia.
      * (* Since need (249) <= remaining (250), we take the left branch *)
        left.
        split.
        -- (* Prove 249 <= 250 *)
           lia.
        -- (* Prove result equality [751; 1] = [502 + 249; 250 - 249] *)
           simpl.
           reflexivity.
Qed.