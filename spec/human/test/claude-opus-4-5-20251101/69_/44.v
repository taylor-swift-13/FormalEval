Require Import ZArith.
Require Import List.
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

Definition test_list := [1; 8; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 3].

Lemma count_1_in_test_list : count_rel 1 test_list 2%nat.
Proof.
  unfold test_list.
  apply cr_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_nil.
Qed.

Lemma count_2_in_test_list : count_rel 2 test_list 3%nat.
Proof.
  unfold test_list.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_nil.
Qed.

Lemma count_3_in_test_list : count_rel 3 test_list 4%nat.
Proof.
  unfold test_list.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_no_match. reflexivity.
  apply cr_match. reflexivity.
  apply cr_nil.
Qed.

Example test_problem_69 : problem_69_spec [1; 8; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 3] 3.
Proof.
  unfold problem_69_spec.
  right. left.
  exists [1; 2; 3].
  exists 3.
  split.
  - discriminate.
  - split.
    + apply fmsr_satisfy with (n := 2%nat).
      * exact count_1_in_test_list.
      * reflexivity.
      * simpl.
        apply fmsr_satisfy with (n := 3%nat).
        -- exact count_2_in_test_list.
        -- reflexivity.
        -- simpl.
           apply fmsr_satisfy with (n := 4%nat).
           ++ exact count_3_in_test_list.
           ++ reflexivity.
           ++ simpl. apply fmsr_nil.
    + split.
      * discriminate.
      * reflexivity.
Qed.