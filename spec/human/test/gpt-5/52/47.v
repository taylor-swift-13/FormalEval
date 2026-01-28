Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list bool) : Prop := True.

Definition problem_52_spec (l : list bool) (t : Z) (output : bool) : Prop :=
  (forall b, In b l -> (if b then 1%Z else 0%Z) < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [true; false; false] 3%Z true.
Proof.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _. intros b HIn.
    simpl in HIn.
    destruct HIn as [Hb | HIn].
    + subst b. simpl. lia.
    + simpl in HIn.
      destruct HIn as [Hb | HIn].
      * subst b. simpl. lia.
      * simpl in HIn.
        destruct HIn as [Hb | HIn].
        { subst b. simpl. lia. }
        { contradiction. }
Qed.