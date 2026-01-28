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

Example test_eat : eat_spec 200 200 252 [400; 52].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 200 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 200 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 252 <= 1000 *)
        lia.
      * (* Since need (200) <= remaining (252), we take the left branch *)
        left.
        split.
        -- (* Prove 200 <= 252 *)
           lia.
        -- (* Prove result equality [400; 52] = [200 + 200; 252 - 200] *)
           simpl.
           reflexivity.
Qed.