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

Example test_eat : eat_spec 800 801 1 [801; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 800 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 801 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 1 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (801) > remaining (1), we take the right branch *)
        right.
        split.
        -- (* Prove 801 > 1 *)
           lia.
        -- (* Prove result equality [801; 0] = [800 + 1; 0] *)
           simpl.
           reflexivity.
Qed.