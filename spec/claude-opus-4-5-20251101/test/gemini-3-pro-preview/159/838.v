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

Example test_eat : eat_spec 501 802 701 [1202; 0].
Proof.
  unfold eat_spec.
  (* 
     The goal is a conjunction of 4 parts. 
     We use split manually to handle them one by one.
  *)
  split.
  - (* Prove 0 <= 501 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 802 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 701 <= 1000 *)
        lia.
      * (* Prove the main logic branch *)
        (* Since need (802) > remaining (701), we take the right branch *)
        right.
        split.
        -- (* Prove 802 > 701 *)
           lia.
        -- (* Prove result equality [1202; 0] = [501 + 701; 0] *)
           simpl.
           reflexivity.
Qed.