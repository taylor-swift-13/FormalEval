Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list bool) : Prop := True.

Definition Z_of_bool (b : bool) : Z := if b then 1%Z else 0%Z.

Definition problem_52_spec (l : list bool) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> Z_of_bool x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [true; false; false] 5%Z true.
Proof.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _. intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx | HIn].
    + subst x. simpl. lia.
    + simpl in HIn. destruct HIn as [Hx | HIn].
      * subst x. simpl. lia.
      * simpl in HIn. destruct HIn as [Hx | HIn].
        { subst x. simpl. lia. }
        { contradiction. }
Qed.