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

Example test_eat : eat_spec 800 1 600 [801; 599].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 800 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 1 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 600 <= 1000 *)
        lia.
      * (* Since need (1) <= remaining (600), we take the left branch *)
        left.
        split.
        -- (* Prove 1 <= 600 *)
           lia.
        -- (* Prove result equality [801; 599] = [800 + 1; 600 - 1] *)
           simpl.
           reflexivity.
Qed.