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

Example test_eat : eat_spec 800 0 599 [800; 599].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one, 
     avoiding the issue where 'repeat split' breaks down the 
     inequalities (like 0 <= 800 <= 1000) into too many subgoals.
  *)
  split.
  - (* Prove 0 <= 800 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 0 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 599 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (0) <= remaining (599), we take the left branch *)
        left.
        split.
        -- (* Prove 0 <= 599 *)
           lia.
        -- (* Prove result equality [800; 599] = [800 + 0; 599 - 0] *)
           simpl.
           reflexivity.
Qed.