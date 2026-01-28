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

Example test_eat : eat_spec 199 749 499 [698; 0].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one, 
     avoiding the issue where 'repeat split' breaks down the 
     inequalities (like 0 <= 199 <= 1000) into too many subgoals.
  *)
  split.
  - (* Prove 0 <= 199 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 749 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 499 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (749) > remaining (499), we take the right branch *)
        right.
        split.
        -- (* Prove 749 > 499 *)
           lia.
        -- (* Prove result equality [698; 0] = [199 + 499; 0] *)
           simpl.
           reflexivity.
Qed.