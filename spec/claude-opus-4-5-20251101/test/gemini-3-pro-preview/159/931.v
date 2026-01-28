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

Example test_eat : eat_spec 703 701 303 [1006; 0].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 703 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 701 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 303 <= 1000 *)
        lia.
      * (* Since need (701) > remaining (303), we take the right branch *)
        right.
        split.
        -- (* Prove 701 > 303 *)
           lia.
        -- (* Prove result equality [1006; 0] = [703 + 303; 0] *)
           simpl.
           reflexivity.
Qed.