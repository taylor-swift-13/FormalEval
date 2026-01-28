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

Ltac solve_count :=
  repeat (
    apply cr_nil ||
    (apply cr_match; [ reflexivity | ]) ||
    (apply cr_no_match; [ reflexivity | ])
  ).

Example test_problem_69 : problem_69_spec [1; 2; 2; 3; 17; 5; 18; 8; 9; 10; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15; 10; 14] 2.
Proof.
  unfold problem_69_spec.
  right. left.
  exists [1; 2; 2; 3; 17; 5; 18; 8; 9; 10; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15; 10; 14]. exists 2.
  split.
  - discriminate.
  - split.
    + (* 1 *)
      eapply fmsr_satisfy.
      * solve_count.
      * simpl. reflexivity.
      * simpl.
      (* 2 *)
      eapply fmsr_satisfy.
      -- solve_count.
      -- simpl. reflexivity.
      -- simpl.
      (* 2 *)
      eapply fmsr_satisfy.
      ++ solve_count.
      ++ simpl. reflexivity.
      ++ simpl.
      (* 3 *)
      eapply fmsr_not_satisfy.
      ** solve_count.
      ** simpl. reflexivity.
      **
      (* 17 *)
      eapply fmsr_not_satisfy.
      --- solve_count.
      --- simpl. reflexivity.
      ---
      (* 5 *)
      eapply fmsr_not_satisfy.
      +++ solve_count.
      +++ simpl. reflexivity.
      +++
      (* 18 *)
      eapply fmsr_not_satisfy.
      *** solve_count.
      *** simpl. reflexivity.
      ***
      (* 8 *)
      eapply fmsr_not_satisfy.
      ---- solve_count.
      ---- simpl. reflexivity.
      ----
      (* 9 *)
      eapply fmsr_not_satisfy.
      ++++ solve_count.
      ++++ simpl. reflexivity.
      ++++
      (* 10 *)
      eapply fmsr_not_satisfy.
      **** solve_count.
      **** simpl. reflexivity.
      ****
      (* 10 *)
      eapply fmsr_not_satisfy.
      ----- solve_count.
      ----- simpl. reflexivity.
      -----
      (* 10 *)
      eapply fmsr_not_satisfy.
      +++++ solve_count.
      +++++ simpl. reflexivity.
      +++++
      (* 10 *)
      eapply fmsr_not_satisfy.
      ***** solve_count.
      ***** simpl. reflexivity.
      *****
      (* 10 *)
      eapply fmsr_not_satisfy.
      ------ solve_count.
      ------ simpl. reflexivity.
      ------
      (* 10 *)
      eapply fmsr_not_satisfy.
      ++++++ solve_count.
      ++++++ simpl. reflexivity.
      ++++++
      (* 11 *)
      eapply fmsr_not_satisfy.
      ****** solve_count.
      ****** simpl. reflexivity.
      ******
      (* 12 *)
      eapply fmsr_not_satisfy.
      ------- solve_count.
      ------- simpl. reflexivity.
      -------
      (* 13 *)
      eapply fmsr_not_satisfy.
      +++++++ solve_count.
      +++++++ simpl. reflexivity.
      +++++++
      (* 14 *)
      eapply fmsr_not_satisfy.
      ******* solve_count.
      ******* simpl. reflexivity.
      *******
      (* 15 *)
      eapply fmsr_not_satisfy.
      -------- solve_count.
      -------- simpl. reflexivity.
      --------
      (* 10 *)
      eapply fmsr_not_satisfy.
      ++++++++ solve_count.
      ++++++++ simpl. reflexivity.
      ++++++++
      (* 14 *)
      eapply fmsr_not_satisfy.
      ******** solve_count.
      ******** simpl. reflexivity.
      ********
      apply fmsr_nil.
    + split.
      * discriminate.
      * reflexivity.
Qed.