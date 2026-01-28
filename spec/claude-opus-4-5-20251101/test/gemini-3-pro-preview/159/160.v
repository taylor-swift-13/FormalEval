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

Example test_eat : eat_spec 501 749 0 [501; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 501 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 749 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 0 <= 1000 *)
        lia.
      * (* Since need (749) > remaining (0), we take the right branch *)
        right.
        split.
        -- (* Prove 749 > 0 *)
           lia.
        -- (* Prove result equality [501; 0] = [501 + 0; 0] *)
           simpl.
           reflexivity.
Qed.