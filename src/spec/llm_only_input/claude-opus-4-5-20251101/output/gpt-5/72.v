Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec (3 :: 2 :: 3 :: nil) 9 true.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros _.
    split.
    + simpl. reflexivity.
    + unfold sum_Z. simpl. lia.
  - intros _. reflexivity.
Qed.