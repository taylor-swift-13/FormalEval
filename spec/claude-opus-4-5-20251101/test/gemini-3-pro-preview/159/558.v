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

Example test_eat : eat_spec 599 701 802 [1300; 101].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 599 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 701 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 802 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (701) <= remaining (802), we take the left branch *)
        left.
        split.
        -- (* Prove 701 <= 802 *)
           lia.
        -- (* Prove result equality [1300; 101] = [599 + 701; 802 - 701] *)
           simpl.
           reflexivity.
Qed.