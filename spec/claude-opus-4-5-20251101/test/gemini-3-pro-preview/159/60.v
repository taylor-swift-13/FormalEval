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

Example test_eat : eat_spec 997 0 3 [997; 3].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 997 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 0 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 3 <= 1000 *)
        lia.
      * (* Since need (0) <= remaining (3), we take the left branch *)
        left.
        split.
        -- (* Prove 0 <= 3 *)
           lia.
        -- (* Prove result equality [997; 3] = [997 + 0; 3 - 0] *)
           simpl.
           reflexivity.
Qed.