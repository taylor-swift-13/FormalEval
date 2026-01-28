Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).

Example test_case : problem_40_spec [1; 2; 3; 4; 5; 2; 4; 5; 5] false.
Proof.
  unfold problem_40_spec.
  split.
  - intros (i & j & k & _ & _ & _ & Hi & Hj & Hk & Hsum).
    assert (Hpos: forall x, In x [1; 2; 3; 4; 5; 2; 4; 5; 5] -> x > 0).
    { intros x HIn. simpl in HIn.
      repeat (destruct HIn as [HIn|HIn]; [subst; lia | ]).
      contradiction. }
    assert (Hvi: nth i [1; 2; 3; 4; 5; 2; 4; 5; 5] 0 > 0).
    { apply Hpos. apply nth_In. simpl in Hi. exact Hi. }
    assert (Hvj: nth j [1; 2; 3; 4; 5; 2; 4; 5; 5] 0 > 0).
    { apply Hpos. apply nth_In. simpl in Hj. exact Hj. }
    assert (Hvk: nth k [1; 2; 3; 4; 5; 2; 4; 5; 5] 0 > 0).
    { apply Hpos. apply nth_In. simpl in Hk. exact Hk. }
    lia.
  - discriminate.
Qed.