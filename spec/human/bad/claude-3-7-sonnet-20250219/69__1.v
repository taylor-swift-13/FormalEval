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

(** Auxiliary count function *)

Fixpoint count (z : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => if Z.eqb h z then S (count z t) else count z t
  end.

Lemma count_rel_count_fix : forall z lst,
  count_rel z lst (count z lst).
Proof.
  intros z lst.
  induction lst as [|h t IH].
  - constructor.
  - simpl.
    destruct (Z.eqb h z) eqn:Heq.
    + apply cr_match; [assumption | apply IH].
    + apply cr_no_match; [assumption | apply IH].
Qed.

(** Example proof for the test case *)

Example test_case_1_correct :
  problem_69_spec [5%Z; 5%Z; 5%Z; 5%Z; 1%Z] 1%Z.
Proof.
  unfold problem_69_spec.
  right. left.
  exists [1%Z; 5%Z].
  split.
  - discriminate.
  - split.
    + (* find_max_satisfying_rel [5;5;5;5;1] [1;5] (-1) 1 *)

      apply fmsr_satisfy with (n := count 1 [5;5;5;5;1]).
      * apply count_rel_count_fix.
      * simpl.
        assert (count 1 [5;5;5;5;1] = 1).
        {
          simpl; repeat (try rewrite Z.eqb_neq by discriminate); rewrite Z.eqb_refl; simpl; reflexivity.
        }
        rewrite H.
        simpl.
        reflexivity.
      * apply fmsr_not_satisfy with (n := count 5 [5;5;5;5;1]).
        -- apply count_rel_count_fix.
        -- simpl.
           assert (count 5 [5;5;5;5;1] = 4).
           {
             simpl; repeat (try rewrite Z.eqb_refl); simpl; repeat (try rewrite Z.eqb_neq by discriminate); reflexivity.
           }
           rewrite H0.
           simpl.
           reflexivity.
        -- apply fmsr_nil.
    + split; [discriminate | reflexivity].
Qed.