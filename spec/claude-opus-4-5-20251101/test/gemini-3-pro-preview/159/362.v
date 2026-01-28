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

Example test_eat : eat_spec 1 300 600 [301; 300].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 1 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 300 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 600 <= 1000 *)
        lia.
      * (* Since need (300) <= remaining (600), we take the left branch *)
        left.
        split.
        -- (* Prove 300 <= 600 *)
           lia.
        -- (* Prove result equality [301; 300] = [1 + 300; 600 - 300] *)
           simpl.
           reflexivity.
Qed.