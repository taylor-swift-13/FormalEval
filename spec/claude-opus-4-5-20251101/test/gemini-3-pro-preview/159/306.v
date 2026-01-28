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

Example test_eat : eat_spec 0 499 599 [499; 100].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 0 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 499 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 599 <= 1000 *)
        lia.
      * (* Since need (499) <= remaining (599), we take the left branch *)
        left.
        split.
        -- (* Prove 499 <= 599 *)
           lia.
        -- (* Prove result equality [499; 100] = [0 + 499; 599 - 499] *)
           simpl.
           reflexivity.
Qed.