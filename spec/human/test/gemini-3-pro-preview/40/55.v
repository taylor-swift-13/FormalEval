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

Example test_case : problem_40_spec [1; 1; 2; 3; 4; 4; -9; 1] false.
Proof.
  unfold problem_40_spec.
  split.
  - intros (i & j & k & Hij & Hik & Hjk & Hi & Hj & Hk & Hsum).
    simpl in Hi, Hj, Hk.
    repeat (destruct i as [|i]; [| try lia]).
    all: repeat (destruct j as [|j]; [| try lia]).
    all: repeat (destruct k as [|k]; [| try lia]).
    all: simpl in Hsum; try lia.
  - discriminate.
Qed.