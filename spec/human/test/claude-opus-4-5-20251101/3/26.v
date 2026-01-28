Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_below_zero_2 : problem_3_spec [30%Z; 1%Z; 1%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hsum]]].
    destruct prefix as [|a prefix'].
    + simpl in Hsum. lia.
    + destruct prefix' as [|b prefix''].
      * simpl in Happ. injection Happ as Ha Hsuffix.
        subst a. simpl in Hsum. lia.
      * destruct prefix'' as [|c prefix'''].
        -- simpl in Happ. injection Happ as Ha Hb Hsuffix.
           subst a b. simpl in Hsum. lia.
        -- destruct prefix''' as [|d prefix''''].
           ++ simpl in Happ. injection Happ as Ha Hb Hc Hsuffix.
              subst a b c. simpl in Hsum. lia.
           ++ simpl in Happ. 
              destruct suffix.
              ** simpl in Happ. discriminate.
              ** discriminate.
  - intros H. discriminate.
Qed.