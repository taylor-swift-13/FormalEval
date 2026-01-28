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

Example test_eat : eat_spec 801 702 801 [1503; 99].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one.
  *)
  split.
  - (* Prove 0 <= 801 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 702 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 801 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (702) <= remaining (801), we take the left branch *)
        left.
        split.
        -- (* Prove 702 <= 801 *)
           lia.
        -- (* Prove result equality [1503; 99] = [801 + 702; 801 - 702] *)
           simpl.
           reflexivity.
Qed.