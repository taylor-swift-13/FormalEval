Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [3; 2; 3] 9 true.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: true = true -> (Palindrome /\ Sum check) *)
    intros _.
    split.
    + (* Check if q = rev q *)
      simpl.
      reflexivity.
    + (* Check if sum_Z q <= w *)
      unfold sum_Z.
      simpl.
      lia.
  - (* Right to Left: (Palindrome /\ Sum check) -> true = true *)
    intros _.
    reflexivity.
Qed.