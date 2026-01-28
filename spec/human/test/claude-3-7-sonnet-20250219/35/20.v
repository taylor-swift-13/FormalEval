Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example problem_35_example :
  problem_35_spec [50; 49; 49; 47; 49] 50.
Proof.
  unfold problem_35_spec.
  split.
  - (* Show 50 ∈ [50; 49; 49; 47; 49] *)
    simpl. left. reflexivity.
  - (* Show ∀ x, x ∈ [50; 49; 49; 47; 49] → x ≤ 50 *)
    intros x H.
    simpl in H.
    destruct H as [H | H].
    + subst x. lia.
    + destruct H as [H | H].
      * subst x. lia.
      * destruct H as [H | H].
        -- subst x. lia.
        -- destruct H as [H | H].
           ++ subst x. lia.
           ++ destruct H as [H | H].
              ** subst x. lia.
              ** simpl in H. contradiction.
Qed.