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

Example test_eat : eat_spec 602 601 749 [1203; 148].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 602 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 601 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 749 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (601) <= remaining (749), we take the left branch *)
        left.
        split.
        -- (* Prove 601 <= 749 *)
           lia.
        -- (* Prove result equality [1203; 148] = [602 + 601; 749 - 601] *)
           simpl.
           reflexivity.
Qed.