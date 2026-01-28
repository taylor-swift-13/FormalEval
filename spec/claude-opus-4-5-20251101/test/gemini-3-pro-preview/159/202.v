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

Example test_eat : eat_spec 700 501 748 [1201; 247].
Proof.
  unfold eat_spec.
  split.
  - (* Prove 0 <= 700 <= 1000 *)
    lia.
  - split.
    + (* Prove 0 <= 501 <= 1000 *)
      lia.
    + split.
      * (* Prove 0 <= 748 <= 1000 *)
        lia.
      * (* Since need (501) <= remaining (748), we take the left branch *)
        left.
        split.
        -- (* Prove 501 <= 748 *)
           lia.
        -- (* Prove result equality [1201; 247] = [700 + 501; 748 - 501] *)
           simpl.
           reflexivity.
Qed.