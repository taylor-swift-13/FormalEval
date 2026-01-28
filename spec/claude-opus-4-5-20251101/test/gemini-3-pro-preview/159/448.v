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

Example test_eat : eat_spec 1 500 503 [501; 3].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 1 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 500 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 503 <= 1000 *)
        lia.
      * (* Since need (500) <= remaining (503), we take the left branch *)
        left.
        split.
        -- (* Prove 500 <= 503 *)
           lia.
        -- (* Prove result equality [501; 3] = [1 + 500; 503 - 500] *)
           simpl.
           reflexivity.
Qed.