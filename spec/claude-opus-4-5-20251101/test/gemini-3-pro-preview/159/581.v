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

Example test_eat : eat_spec 250 251 250 [500; 0].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one.
  *)
  split.
  - (* Prove 0 <= 250 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 251 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 250 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (251) > remaining (250), we take the right branch *)
        right.
        split.
        -- (* Prove 251 > 250 *)
           lia.
        -- (* Prove result equality [500; 0] = [250 + 250; 0] *)
           simpl.
           reflexivity.
Qed.