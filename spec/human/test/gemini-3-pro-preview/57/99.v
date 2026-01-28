Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example test_monotonic : problem_57_spec [10; 9; 8; 7; 8; 7; 7; 7] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + inversion Hinc as [| ? ? Htail Hrel]; subst.
      inversion Hrel; subst.
      lia.
    + inversion Hdec as [| ? ? Htail1 Hrel1]; subst.
      inversion Htail1 as [| ? ? Htail2 Hrel2]; subst.
      inversion Htail2 as [| ? ? Htail3 Hrel3]; subst.
      inversion Htail3 as [| ? ? Htail4 Hrel4]; subst.
      inversion Hrel4; subst.
      lia.
Qed.