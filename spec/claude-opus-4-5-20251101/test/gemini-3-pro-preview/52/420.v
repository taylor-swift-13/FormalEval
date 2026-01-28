Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [0.2%R; 62.5%R; -63.579573934400166%R; 0.5%R; 98.82739614126038%R; -0.28791951724548404%R; -50.78504214587984%R; 58.062454697705476%R; 55.110190228263775%R; 10.520189946545017%R] 0%R false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. inversion H.
  - intros H.
    assert (In 0.2%R [0.2%R; 62.5%R; -63.579573934400166%R; 0.5%R; 98.82739614126038%R; -0.28791951724548404%R; -50.78504214587984%R; 58.062454697705476%R; 55.110190228263775%R; 10.520189946545017%R]) as HIn.
    { simpl. left. reflexivity. }
    apply H in HIn.
    lra.
Qed.