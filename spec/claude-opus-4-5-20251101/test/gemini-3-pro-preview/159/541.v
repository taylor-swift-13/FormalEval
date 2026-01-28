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

Example test_eat : eat_spec 199 498 600 [697; 102].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 199 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 498 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 600 <= 1000 *)
        lia.
      * (* Since need (498) <= remaining (600), we take the left branch *)
        left.
        split.
        -- (* Prove 498 <= 600 *)
           lia.
        -- (* Prove result equality [697; 102] = [199 + 498; 600 - 498] *)
           simpl.
           reflexivity.
Qed.