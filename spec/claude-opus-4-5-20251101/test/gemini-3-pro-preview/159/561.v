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

Example test_eat : eat_spec 999 601 599 [1598; 0].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one.
  *)
  split.
  - (* Prove 0 <= 999 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 601 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 599 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (601) > remaining (599), we take the right branch *)
        right.
        split.
        -- (* Prove 601 > 599 *)
           lia.
        -- (* Prove result equality [1598; 0] = [999 + 599; 0] *)
           simpl.
           reflexivity.
Qed.