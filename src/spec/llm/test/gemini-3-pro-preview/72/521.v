Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [7; 1; 2; 1; 0; 0; 0] 30 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [Hpal _].
    (* Verify q <> rev q to show contradiction *)
    simpl in Hpal.
    discriminate.
Qed.