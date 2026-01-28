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

Example test_eat : eat_spec 504 1 200 [505; 199].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one, 
     avoiding the issue where 'repeat split' breaks down the 
     inequalities (like 0 <= 504 <= 1000) into too many subgoals.
  *)
  split.
  - (* Prove 0 <= 504 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 1 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 200 <= 1000 *)
        lia.
      * (* Since need (1) <= remaining (200), we take the left branch *)
        left.
        split.
        -- (* Prove 1 <= 200 *)
           lia.
        -- (* Prove result equality [505; 199] = [504 + 1; 200 - 1] *)
           simpl.
           reflexivity.
Qed.