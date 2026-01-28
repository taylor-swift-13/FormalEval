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

Example test_eat : eat_spec 1 10 10 [11; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 1 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 10 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 10 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (10) <= remaining (10), we take the left branch *)
        left.
        split.
        -- (* Prove 10 <= 10 *)
           lia.
        -- (* Prove result equality [11; 0] = [1 + 10; 10 - 10] *)
           simpl.
           reflexivity.
Qed.