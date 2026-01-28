Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [2000000%Z; 10000000%Z; 9000000%Z; 10%Z; 8000000%Z; 6000000%Z; 2000000%Z; 8000000%Z] 10000001%Z true.
Proof.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _. intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx1 | HIn1].
    + subst x. lia.
    + simpl in HIn1. destruct HIn1 as [Hx2 | HIn2].
      * subst x. lia.
      * simpl in HIn2. destruct HIn2 as [Hx3 | HIn3].
        { subst x. lia. }
        { simpl in HIn3. destruct HIn3 as [Hx4 | HIn4].
          - subst x. lia.
          - simpl in HIn4. destruct HIn4 as [Hx5 | HIn5].
            + subst x. lia.
            + simpl in HIn5. destruct HIn5 as [Hx6 | HIn6].
              * subst x. lia.
              * simpl in HIn6. destruct HIn6 as [Hx7 | HIn7].
                { subst x. lia. }
                { simpl in HIn7. destruct HIn7 as [Hx8 | HIn8].
                  - subst x. lia.
                  - simpl in HIn8. inversion HIn8. } }
Qed.