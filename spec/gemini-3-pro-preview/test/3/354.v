Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_new : below_zero_spec [1%Z; -1%Z; 1%Z; -1%Z; 20%Z; 1%Z; -1%Z; 26%Z; -1%Z; 1%Z; 7%Z; -3%Z; 1%Z; -1%Z; 1%Z; -1%Z; -2%Z; -1%Z; 1%Z; -1%Z; 1%Z; -29%Z; -2%Z; 1%Z; -1%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    (* We check each possible length n from 1 to 25. 
       do 26 covers n=0 to n=25. n=0 is handled by bounds check in lia. 
       n=1..25 are handled by checking the sum in lia. *)
    do 26 (destruct n; [ simpl in Hsum; try lia | ]).
    (* Handle the case where n > 25 *)
    simpl in Hbounds. lia.
Qed.