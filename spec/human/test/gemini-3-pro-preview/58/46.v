Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_58_pre (l1 l2 : list R) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list R) : Prop :=
  (forall x: R, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Rle l_out /\
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [72.37521383648374%R; 75.77463522981091%R; -68.50801238200772%R; -16.457158264907306%R; -14.710649879972792%R; -50.826346308865425%R; 94.08151854781187%R; 62.25940015569594%R; -16.457158264907306%R]
    [72.37521383648374%R; 75.77463522981091%R; -68.50801238200772%R; -16.457158264907306%R; -14.710649879972792%R; -50.826346308865425%R; 94.08151854781187%R; 62.25940015569594%R; -16.457158264907306%R]
    [-68.50801238200772%R; -50.826346308865425%R; -16.457158264907306%R; -14.710649879972792%R; 62.25940015569594%R; 72.37521383648374%R; 75.77463522981091%R; 94.08151854781187%R].
Proof.
  unfold problem_58_spec.
  split.
  - intro x; split.
    + intro H.
      simpl in H.
      repeat destruct H as [H|H]; subst; simpl; split; auto 20.
    + intros [H1 H2].
      simpl in H1.
      repeat destruct H1 as [H1|H1]; subst.
      all: try (simpl; auto 20; fail).
      all: exfalso; repeat destruct H2 as [H2|H2]; try lra; try contradiction.
  - split.
    + repeat constructor.
      all: simpl; try lra.
    + repeat constructor.
      all: simpl; intuition lra.
Qed.