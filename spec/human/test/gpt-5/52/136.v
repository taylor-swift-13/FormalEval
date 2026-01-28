Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [100%Z; -200%Z; -400%Z; 500%Z; -600%Z] 8000002%Z true.
Proof.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _. intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx | HIn].
    + subst x. lia.
    + simpl in HIn. destruct HIn as [Hx | HIn].
      * subst x. lia.
      * simpl in HIn. destruct HIn as [Hx | HIn].
        { subst x. lia. }
        { simpl in HIn. destruct HIn as [Hx | HIn].
          - subst x. lia.
          - simpl in HIn. destruct HIn as [Hx | HIn].
            + subst x. lia.
            + contradiction. }
Qed.