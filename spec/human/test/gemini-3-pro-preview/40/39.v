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

Example test_case : problem_40_spec [1; 2; 3; 4; 5; 4] false.
Proof.
  unfold problem_40_spec.
  split.
  - intros (i & j & k & Hij & Hik & Hjk & Hi & Hj & Hk & Hsum).
    simpl in Hi, Hj, Hk.
    assert (Hpos : forall n, (n < 6)%nat -> nth n [1; 2; 3; 4; 5; 4] 0 >= 1).
    { intros n Hn.
      repeat (destruct n as [|n]; [simpl; lia | try lia]). }
    assert (Hi_val : nth i [1; 2; 3; 4; 5; 4] 0 >= 1) by (apply Hpos; lia).
    assert (Hj_val : nth j [1; 2; 3; 4; 5; 4] 0 >= 1) by (apply Hpos; lia).
    assert (Hk_val : nth k [1; 2; 3; 4; 5; 4] 0 >= 1) by (apply Hpos; lia).
    lia.
  - discriminate.
Qed.