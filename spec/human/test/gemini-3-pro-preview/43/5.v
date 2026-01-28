Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `pairs_sum_to_zero` *)
Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j)  /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_problem_43 : problem_43_spec [1] false.
Proof.
  unfold problem_43_spec.
  split; intro H.
  - destruct H as [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    lia.
  - discriminate H.
Qed.