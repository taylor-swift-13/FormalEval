Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [1; 1; 1; 1; 1; 1; 1] 7 true.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right implication *)
    intros _.
    split.
    + (* Check palindrome *)
      simpl.
      reflexivity.
    + (* Check sum *)
      unfold sum_Z.
      simpl.
      discriminate.
  - (* Right to Left implication *)
    intros _.
    reflexivity.
Qed.