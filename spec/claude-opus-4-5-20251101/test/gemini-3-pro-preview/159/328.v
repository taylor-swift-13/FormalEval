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

Example test_eat : eat_spec 602 602 699 [1204; 97].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 602 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 602 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 699 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (602) <= remaining (699), we take the left branch *)
        left.
        split.
        -- (* Prove 602 <= 699 *)
           lia.
        -- (* Prove result equality [1204; 97] = [602 + 602; 699 - 602] *)
           simpl.
           reflexivity.
Qed.