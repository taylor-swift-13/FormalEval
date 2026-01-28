Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Definition sum_R (l : list R) : R := fold_right Rplus 0%R l.

Definition will_it_fly_spec (q : list R) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_R q <= IZR w.

Example test_will_it_fly : will_it_fly_spec [48.77540799744989%R; -48.319352731351685%R; -3.8838243003108204%R; -48.319352731351685%R] 2%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right implication: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left implication: ... -> false = true *)
    intros [Hrev Hsum].
    (* The list is not a palindrome, so Hrev should be contradictory *)
    simpl in Hrev.
    inversion Hrev.
    (* The first equality from inversion is 48.77... = -48.31... *)
    (* lra can solve this contradiction on Reals *)
    lra.
Qed.