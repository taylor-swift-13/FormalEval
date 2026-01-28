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

Example test_eat : eat_spec 601 601 750 [1202; 149].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 601 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 601 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 750 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (601) <= remaining (750), we take the left branch *)
        left.
        split.
        -- (* Prove 601 <= 750 *)
           lia.
        -- (* Prove result equality [1202; 149] = [601 + 601; 750 - 601] *)
           simpl.
           reflexivity.
Qed.