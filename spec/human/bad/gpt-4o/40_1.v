Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Specification of triples_sum_to_zero function *)
Definition triples_sum_to_zero (input : list Z) : bool :=
  let fix find_triple lst :=
      match lst with
      | [] => false
      | x :: xs =>
          let fix check_with_others ys :=
              match ys with
              | [] => find_triple xs
              | y :: ys' =>
                  let fix check_third zs :=
                      match zs with
                      | [] => check_with_others ys'
                      | z :: zs' =>
                          if (x + y + z =? 0)%Z
                          then true
                          else check_third zs'
                      end
                  in check_third xs
              end
          in check_with_others xs
      end
  in find_triple input.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).

Example test_case_1 : triples_sum_to_zero [1%Z; 3%Z; 5%Z; 0%Z] = false.
Proof.
  unfold triples_sum_to_zero.
  simpl.
  reflexivity.
Qed.

Example test_case_2 : triples_sum_to_zero [1%Z; 3%Z; -2%Z; 1%Z] = true.
Proof.
  unfold triples_sum_to_zero.
  simpl.
  reflexivity.
Qed.

Example test_case_3 : triples_sum_to_zero [1%Z; 2%Z; 3%Z; 7%Z] = false.
Proof.
  unfold triples_sum_to_zero.
  simpl.
  reflexivity.
Qed.

Example test_case_4 : triples_sum_to_zero [2%Z; 4%Z; -5%Z; 3%Z; 9%Z; 7%Z] = true.
Proof.
  unfold triples_sum_to_zero.
  simpl.
  reflexivity.
Qed.

Example test_case_5 : triples_sum_to_zero [1%Z] = false.
Proof.
  unfold triples_sum_to_zero.
  simpl.
  reflexivity.
Qed.

(* Verify the specification against the function for a given test case *)
Lemma test_case_1_spec : problem_40_spec [1%Z; 3%Z; 5%Z; 0%Z] false.
Proof.
  unfold problem_40_spec.
  split; intros.
  - destruct H as [i [j [k [Hneq1 [Hneq2 [Hneq3 [Hi [Hj [Hk Heq]]]]]]]]].
    simpl in Hi, Hj, Hk.
    destruct i, j, k; simpl in *; try lia.
    + rewrite Z.add_0_r in Heq. lia.
    + rewrite Z.add_0_r in Heq. lia.
    + lia.
  - simpl in H. discriminate.
Qed.