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

Example test_eat : eat_spec 600 603 2 [602; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 600 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 603 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 2 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (603) > remaining (2), we take the right branch *)
        right.
        split.
        -- (* Prove 603 > 2 *)
           lia.
        -- (* Prove result equality [602; 0] = [600 + 2; 0] *)
           simpl.
           reflexivity.
Qed.