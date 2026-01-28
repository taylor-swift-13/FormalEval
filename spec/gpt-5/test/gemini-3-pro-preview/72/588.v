Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [6; 3; 3; 2; 1; 0; 1] 7 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: ... -> false = true *)
    intros [Hpal Hsum].
    (* Check palindrome: [6; 3; 3; 2; 1; 0; 1] = rev ... *)
    simpl in Hpal.
    (* The list is not a palindrome (6 <> 1), so Hpal is False *)
    discriminate Hpal.
Qed.