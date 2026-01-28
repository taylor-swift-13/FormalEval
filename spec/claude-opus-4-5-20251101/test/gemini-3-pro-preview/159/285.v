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

Example test_eat : eat_spec 500 501 501 [1001; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 500 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 501 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 501 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (501) <= remaining (501), we take the left branch *)
        left.
        split.
        -- (* Prove 501 <= 501 *)
           lia.
        -- (* Prove result equality [1001; 0] = [500 + 501; 501 - 501] *)
           simpl.
           reflexivity.
Qed.