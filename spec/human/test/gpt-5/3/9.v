Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_1_2_3_minus6 : problem_3_spec [1%Z; 2%Z; 3%Z; -6%Z] false.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|x prefix'].
    + simpl in Happ. subst suffix.
      simpl in Hlt. lia.
    + simpl in Happ.
      injection Happ as Hhd1 Htail1. subst x.
      destruct prefix' as [|y prefix''].
      * simpl in Htail1. subst suffix. simpl in Hlt. lia.
      * simpl in Htail1.
        injection Htail1 as Hhd2 Htail2. subst y.
        destruct prefix'' as [|z prefix'''].
        -- simpl in Htail2. subst suffix. simpl in Hlt. lia.
        -- simpl in Htail2.
           injection Htail2 as Hhd3 Htail3. subst z.
           destruct prefix''' as [|t prefix''''].
           --- simpl in Htail3. subst suffix. simpl in Hlt. lia.
           --- simpl in Htail3.
               injection Htail3 as Hhd4 Htail4. subst t.
               destruct prefix'''' as [|u prefix'''''].
               ---- simpl in Htail4. subst suffix. simpl in Hlt. lia.
               ---- simpl in Htail4. discriminate.
  - intros Hfalse. exfalso. discriminate.
Qed.