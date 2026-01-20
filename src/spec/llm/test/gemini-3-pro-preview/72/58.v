Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [1; 2; 13; 1] 1 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [Hpal Hsum].
    unfold sum_list in Hsum.
    simpl in Hsum.
    (* Hsum reduces to 17 <= 1, which is false *)
    lia.
Qed.