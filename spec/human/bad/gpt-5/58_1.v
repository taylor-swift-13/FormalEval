Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Z.le l_out /\
  NoDup l_out.

Example problem_58_test :
  problem_58_spec
    [1%Z; 4%Z; 3%Z; 34%Z; 653%Z; 2%Z; 5%Z]
    [5%Z; 7%Z; 1%Z; 5%Z; 9%Z; 653%Z; 121%Z]
    [1%Z; 5%Z; 653%Z].
Proof.
  unfold problem_58_spec.
  split.
  (* membership equivalence *)
  intros x; split.
  (* -> direction *)
  simpl. intros Hin.
  destruct Hin as [Hx|[Hx|[Hx|Hnil]]]; try contradiction; subst; split; simpl; auto.
  (* <- direction *)
  intros [H1 H2].
  simpl in H2.
  destruct H2 as [H2|H2].
  { subst. simpl. auto. }
  destruct H2 as [H2|H2].
  { subst. exfalso.
    simpl in H1.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    contradiction. }
  destruct H2 as [H2|H2].
  { subst. simpl. auto. }
  destruct H2 as [H2|H2].
  { subst. simpl. auto. }
  destruct H2 as [H2|H2].
  { subst. exfalso.
    simpl in H1.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    contradiction. }
  destruct H2 as [H2|H2].
  { subst. simpl. auto. }
  destruct H2 as [H2|H2].
  { subst. exfalso.
    simpl in H1.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    destruct H1 as [H1|H1]; try lia.
    contradiction. }
  contradiction.
  (* Sorted and NoDup *)
  split.
  (* Sorted Z.le [1;5;653] *)
  assert (Sorted Z.le [653%Z]) as S653.
  { constructor.
    - constructor.
    - constructor. }
  assert (Sorted Z.le [5%Z; 653%Z]) as S5_653.
  { constructor.
    - constructor.
      + lia.
      + constructor.
    - exact S653. }
  constructor.
  - constructor.
    + lia.
    + constructor.
      * lia.
      * constructor.
  - exact S5_653.
  (* NoDup [1;5;653] *)
  constructor.
  - intros Hin. simpl in Hin.
    destruct Hin as [H|[H|Hnil]].
    + subst. lia.
    + destruct H as [H|Hnil'].
      * subst. lia.
      * contradiction.
    + contradiction.
  - constructor.
    + intros Hin. simpl in Hin.
      destruct Hin as [H|Hnil]; [subst; lia | contradiction].
    + constructor.
      * intros Hin. simpl in Hin. contradiction.
      * constructor.
Qed.