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

Example test_eat : eat_spec 600 749 750 [1349; 1].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one, 
     avoiding the issue where 'repeat split' breaks down the 
     inequalities (like 0 <= 600 <= 1000) into too many subgoals.
  *)
  split.
  - (* Prove 0 <= 600 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 749 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 750 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (749) <= remaining (750), we take the left branch *)
        left.
        split.
        -- (* Prove 749 <= 750 *)
           lia.
        -- (* Prove result equality [1349; 1] = [600 + 749; 750 - 749] *)
           simpl.
           reflexivity.
Qed.