Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [1; 4; 2; 5; 3; 2; 1; 1] 15 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right implication: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left implication: ... -> false = true *)
    intros [Hpal Hsum].
    unfold sum_Z in Hsum.
    simpl in Hsum.
    (* Hsum is now 19 <= 15, which reduces to False in ZArith *)
    elim Hsum.
    reflexivity.
Qed.