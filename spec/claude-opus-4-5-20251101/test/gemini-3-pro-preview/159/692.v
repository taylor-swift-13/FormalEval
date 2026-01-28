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

Example test_eat : eat_spec 200 199 200 [399; 1].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one, 
     avoiding the issue where 'repeat split' breaks down the 
     inequalities (like 0 <= 200 <= 1000) into too many subgoals.
  *)
  split.
  - (* Prove 0 <= 200 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 199 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 200 <= 1000 *)
        lia.
      * (* Since need (199) <= remaining (200), we take the left branch *)
        left.
        split.
        -- (* Prove 199 <= 200 *)
           lia.
        -- (* Prove result equality [399; 1] = [200 + 199; 200 - 199] *)
           simpl.
           reflexivity.
Qed.