Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Inductive count_rel : Z -> list Z -> nat -> Prop :=
  | cr_nil : forall z, count_rel z [] 0
  | cr_match : forall z h t n,
      Z.eqb z h = true ->
      count_rel z t n ->
      count_rel z (h :: t) (S n)
  | cr_no_match : forall z h t n,
      Z.eqb z h = false ->
      count_rel z t n ->
      count_rel z (h :: t) n.

Inductive find_max_satisfying_rel : list Z -> list Z -> Z -> Z -> Prop :=
  | fmsr_nil : forall lst current_max, find_max_satisfying_rel lst [] current_max current_max
  | fmsr_satisfy : forall lst h t current_max result n,
      count_rel h lst n ->
      (Z.of_nat n >=? h) = true ->
      find_max_satisfying_rel lst t (Z.max h current_max) result ->
      find_max_satisfying_rel lst (h :: t) current_max result
  | fmsr_not_satisfy : forall lst h t current_max result n,
      count_rel h lst n ->
      (Z.of_nat n >=? h) = false ->
      find_max_satisfying_rel lst t current_max result ->
      find_max_satisfying_rel lst (h :: t) current_max result.

Definition problem_69_pre (lst : list Z) : Prop := lst <> []%list /\ (forall x, In x lst -> (x > 0)%Z).

Definition problem_69_spec (lst : list Z) (y : Z) : Prop :=
  (lst = [] /\ y = (-1)%Z) \/
  (exists candidates max_val,
     lst <> [] /\
     find_max_satisfying_rel lst candidates (-1)%Z max_val /\
     max_val <> (-1)%Z /\
     y = max_val) \/
  (exists candidates max_val,
     lst <> [] /\
     find_max_satisfying_rel lst candidates (-1)%Z max_val /\
     max_val = (-1)%Z /\
     y = (-1)%Z).

Example problem_69_test_1 :
  problem_69_spec ([4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 3%Z; 5%Z; 5%Z; 4%Z]) ((-1)%Z).
Proof.
  right; right.
  exists [4%Z; 5%Z; 6%Z; 3%Z], (-1)%Z.
  split.
  { discriminate. }
  split.
  { assert (Hc4: count_rel 4%Z [4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 3%Z; 5%Z; 5%Z; 4%Z] 3%nat).
    { eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      apply cr_nil. }
    assert (Hc5: count_rel 5%Z [4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 3%Z; 5%Z; 5%Z; 4%Z] 4%nat).
    { eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      apply cr_nil. }
    assert (Hc6: count_rel 6%Z [4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 3%Z; 5%Z; 5%Z; 4%Z] 1%nat).
    { eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      apply cr_nil. }
    assert (Hc3: count_rel 3%Z [4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 3%Z; 5%Z; 5%Z; 4%Z] 1%nat).
    { eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      eapply cr_no_match; [now compute|].
      apply cr_nil. }
    eapply fmsr_not_satisfy with (n := 3%nat).
    - exact Hc4.
    - now compute.
    - eapply fmsr_not_satisfy with (n := 4%nat).
      + exact Hc5.
      + now compute.
      + eapply fmsr_not_satisfy with (n := 1%nat).
        * exact Hc6.
        * now compute.
        * eapply fmsr_not_satisfy with (n := 1%nat).
          { exact Hc3. }
          { now compute. }
          { apply fmsr_nil. } }
  split.
  { reflexivity. }
  { reflexivity. }
Qed.