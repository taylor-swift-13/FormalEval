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

Example test_eat : eat_spec 500 299 500 [799; 201].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 500 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 299 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 500 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (299) <= remaining (500), we take the left branch *)
        left.
        split.
        -- (* Prove 299 <= 500 *)
           lia.
        -- (* Prove result equality [799; 201] = [500 + 299; 500 - 299] *)
           simpl.
           reflexivity.
Qed.