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

Example test_eat : eat_spec 499 301 499 [800; 198].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 499 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 301 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 499 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (301) <= remaining (499), we take the left branch *)
        left.
        split.
        -- (* Prove 301 <= 499 *)
           lia.
        -- (* Prove result equality [800; 198] = [499 + 301; 499 - 301] *)
           simpl.
           reflexivity.
Qed.