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

Example test_eat : eat_spec 799 198 301 [997; 103].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 799 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 198 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 301 <= 1000 *)
        lia.
      * (* Since need (198) <= remaining (301), we take the left branch *)
        left.
        split.
        -- (* Prove 198 <= 301 *)
           lia.
        -- (* Prove result equality [997; 103] = [799 + 198; 301 - 198] *)
           simpl.
           reflexivity.
Qed.