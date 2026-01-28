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

Example test_eat : eat_spec 601 997 501 [1102; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 601 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 997 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 501 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (997) > remaining (501), we take the right branch *)
        right.
        split.
        -- (* Prove 997 > 501 *)
           lia.
        -- (* Prove result equality [1102; 0] = [601 + 501; 0] *)
           simpl.
           reflexivity.
Qed.