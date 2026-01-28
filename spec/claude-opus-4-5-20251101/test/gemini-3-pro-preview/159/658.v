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

Example test_eat : eat_spec 300 600 601 [900; 1].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 300 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 600 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 601 <= 1000 *)
        lia.
      * (* Since need (600) <= remaining (601), we take the left branch *)
        left.
        split.
        -- (* Prove 600 <= 601 *)
           lia.
        -- (* Prove result equality [900; 1] = [300 + 600; 601 - 600] *)
           simpl.
           reflexivity.
Qed.