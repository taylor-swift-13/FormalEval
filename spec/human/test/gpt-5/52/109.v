Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [10000000%Z; 9000000%Z; 8000001%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z] 10000001%Z true.
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
            + simpl in HIn. destruct HIn as [Hx | HIn].
              * subst x. lia.
              * simpl in HIn. destruct HIn as [Hx | HFalse].
                { subst x. lia. }
                { contradiction. } }
Qed.