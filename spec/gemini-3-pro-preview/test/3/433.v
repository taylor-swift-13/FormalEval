Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_complex : below_zero_spec [1; 2; 3; 4; 5; 30; -15; 0; 7; 6; 29; 8; 0; 7; 21; -18; 1; 4; 6]%Z false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    destruct n as [|n]; [ lia | ].
    do 19 (destruct n as [|n]; [ simpl in Hsum; lia | ]).
    simpl in Hbounds. lia.
Qed.