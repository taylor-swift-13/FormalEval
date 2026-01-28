Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [4; 2; 3; 1; 1; 1] 0 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right implication: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left implication: ... -> false = true *)
    intros [Hpal _].
    (* The list is not a palindrome, so Hpal leads to a contradiction *)
    simpl in Hpal.
    discriminate Hpal.
Qed.