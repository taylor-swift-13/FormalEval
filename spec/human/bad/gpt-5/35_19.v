Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_pre_example :
  problem_35_pre [50%Z; -2%Z; 49%Z; 49%Z; 47%Z; 47%Z; 49%Z; 47%Z].
Proof.
  unfold problem_35_pre.
  discriminate.
Qed.

Example problem_35_spec_example :
  problem_35_spec [50%Z; -2%Z; 49%Z; 49%Z; 47%Z; 47%Z; 49%Z; 47%Z] 50%Z.
Proof.
  split.
  - simpl. left. reflexivity.
  - intros x Hin.
    simpl in Hin.
    destruct Hin as [Hx|Hin].
    + subst. lia.
    + destruct Hin as [Hx|Hin].
      * subst. lia.
      * destruct Hin as [Hx|Hin].
        -- subst. lia.
        -- destruct Hin as [Hx|Hin].
           ++ subst. lia.
           ++ destruct Hin as [Hx|Hin].
              ** subst. lia.
              ** destruct Hin as [Hx|Hin].
                 --- subst. lia.
                 --- destruct Hin as [Hx|Hin].
                     **** subst. lia.
                     **** inversion Hin.
Qed.