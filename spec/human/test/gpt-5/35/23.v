Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_pre_example :
  problem_35_pre [-1%Z; -2%Z; -3%Z; -4%Z; 0%Z].
Proof.
  unfold problem_35_pre.
  discriminate.
Qed.

Example problem_35_spec_example :
  problem_35_spec [-1%Z; -2%Z; -3%Z; -4%Z; 0%Z] 0%Z.
Proof.
  split.
  - simpl. right. right. right. right. left. reflexivity.
  - intros x Hin.
    simpl in Hin.
    destruct Hin as [Hx|Hin].
    + subst. lia.
    + destruct Hin as [Hx|Hin].
      * subst. lia.
      * destruct Hin as [Hx|Hin].
        -- subst. lia.
        -- destruct Hin as [Hx|Hin].
          ** subst. lia.
          ** destruct Hin as [Hx|Hin].
            --- subst. lia.
            --- inversion Hin.
Qed.