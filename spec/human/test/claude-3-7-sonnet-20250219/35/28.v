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
  problem_35_spec [49; 49; 47; 47; 49] 49.
Proof.
  unfold problem_35_spec.
  split.
  - (* Show 49 ∈ [49; 49; 47; 47; 49] *)
    simpl. left. reflexivity.
  - (* Show ∀ x, x ∈ [49; 49; 47; 47; 49] → x ≤ 49 *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]).
    + subst x; lia.
    + subst x; lia.
    + subst x; lia.
    + subst x; lia.
    + subst x; lia.
    + contradiction.
Qed.