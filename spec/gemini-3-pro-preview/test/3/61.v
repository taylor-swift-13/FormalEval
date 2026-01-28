Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_mixed : below_zero_spec [10%Z; 30%Z; -40%Z; 50%Z; 6%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Left to right implication: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to left implication: (exists n, ...) -> false = true *)
    intros [n [Hbounds Hsum]].
    simpl in Hbounds.
    (* Check each possible n from 0 to 5, and the remaining case n > 5 *)
    do 6 (destruct n as [|n]; [ simpl in Hsum; try lia | ]).
    (* Case n > 5 contradicts bounds *)
    lia.
Qed.