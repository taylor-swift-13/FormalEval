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

Example test_eat : eat_spec 747 699 601 [1348; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 747 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 699 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 601 <= 1000 *)
        lia.
      * (* Since need (699) > remaining (601), we take the right branch *)
        right.
        split.
        -- (* Prove 699 > 601 *)
           lia.
        -- (* Prove result equality [1348; 0] = [747 + 601; 0] *)
           simpl.
           reflexivity.
Qed.