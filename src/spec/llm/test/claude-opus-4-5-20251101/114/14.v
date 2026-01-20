Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_subarray {A : Type} (sub arr : list A) : Prop :=
  exists prefix suffix, arr = prefix ++ sub ++ suffix.

Definition non_empty {A : Type} (l : list A) : Prop :=
  l <> [].

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition minSubArraySum_spec (nums : list Z) (result : Z) : Prop :=
  nums <> [] /\
  (exists sub : list Z, 
    non_empty sub /\ 
    is_subarray sub nums /\ 
    sum_list sub = result) /\
  (forall sub : list Z, 
    non_empty sub -> 
    is_subarray sub nums -> 
    result <= sum_list sub).

Lemma sum_list_app : forall l1 l2 : list Z,
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  induction l1 as [|h t IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma subarray_of_input : forall sub prefix suffix,
  [4; -4; -5; -3; 5; -1; 6] = prefix ++ sub ++ suffix ->
  is_subarray sub [4; -4; -5; -3; 5; -1; 6].
Proof.
  intros sub prefix suffix H.
  exists prefix, suffix. exact H.
Qed.

Lemma min_subarray_sum_is_minus12 : forall sub : list Z,
  non_empty sub ->
  is_subarray sub [4; -4; -5; -3; 5; -1; 6] ->
  -12 <= sum_list sub.
Proof.
  intros sub Hne [prefix [suffix Heq]].
  destruct prefix as [|p0 prefix'].
  - simpl in Heq.
    destruct sub as [|s0 sub'].
    + unfold non_empty in Hne. exfalso. apply Hne. reflexivity.
    + injection Heq as Hs0 Hrest.
      subst s0.
      destruct sub' as [|s1 sub''].
      * simpl. lia.
      * injection Hrest as Hs1 Hrest'.
        subst s1.
        destruct sub'' as [|s2 sub'''].
        { simpl. lia. }
        injection Hrest' as Hs2 Hrest''.
        subst s2.
        destruct sub''' as [|s3 sub''''].
        { simpl. lia. }
        injection Hrest'' as Hs3 Hrest'''.
        subst s3.
        destruct sub'''' as [|s4 sub'''''].
        { simpl. lia. }
        injection Hrest''' as Hs4 Hrest''''.
        subst s4.
        destruct sub''''' as [|s5 sub''''''].
        { simpl. lia. }
        injection Hrest'''' as Hs5 Hrest'''''.
        subst s5.
        destruct sub'''''' as [|s6 sub'''''''].
        { simpl. lia. }
        injection Hrest''''' as Hs6 Hrest''''''.
        subst s6.
        destruct sub''''''' as [|s7 sub''''''''].
        { simpl. lia. }
        destruct suffix; discriminate Hrest''''''.
  - injection Heq as Hp0 Hrest.
    subst p0.
    destruct prefix' as [|p1 prefix''].
    + simpl in Hrest.
      destruct sub as [|s0 sub'].
      * unfold non_empty in Hne. exfalso. apply Hne. reflexivity.
      * injection Hrest as Hs0 Hrest'.
        subst s0.
        destruct sub' as [|s1 sub''].
        { simpl. lia. }
        injection Hrest' as Hs1 Hrest''.
        subst s1.
        destruct sub'' as [|s2 sub'''].
        { simpl. lia. }
        injection Hrest'' as Hs2 Hrest'''.
        subst s2.
        destruct sub''' as [|s3 sub''''].
        { simpl. lia. }
        injection Hrest''' as Hs3 Hrest''''.
        subst s3.
        destruct sub'''' as [|s4 sub'''''].
        { simpl. lia. }
        injection Hrest'''' as Hs4 Hrest'''''.
        subst s4.
        destruct sub''''' as [|s5 sub''''''].
        { simpl. lia. }
        injection Hrest''''' as Hs5 Hrest''''''.
        subst s5.
        destruct sub'''''' as [|s6 sub'''''''].
        { simpl. lia. }
        destruct suffix; discriminate Hrest''''''.
    + injection Hrest as Hp1 Hrest'.
      subst p1.
      destruct prefix'' as [|p2 prefix'''].
      * simpl in Hrest'.
        destruct sub as [|s0 sub'].
        { unfold non_empty in Hne. exfalso. apply Hne. reflexivity. }
        injection Hrest' as Hs0 Hrest''.
        subst s0.
        destruct sub' as [|s1 sub''].
        { simpl. lia. }
        injection Hrest'' as Hs1 Hrest'''.
        subst s1.
        destruct sub'' as [|s2 sub'''].
        { simpl. lia. }
        injection Hrest''' as Hs2 Hrest''''.
        subst s2.
        destruct sub''' as [|s3 sub''''].
        { simpl. lia. }
        injection Hrest'''' as Hs3 Hrest'''''.
        subst s3.
        destruct sub'''' as [|s4 sub'''''].
        { simpl. lia. }
        injection Hrest''''' as Hs4 Hrest''''''.
        subst s4.
        destruct sub''''' as [|s5 sub''''''].
        { simpl. lia. }
        destruct suffix; discriminate Hrest''''''.
      * injection Hrest' as Hp2 Hrest''.
        subst p2.
        destruct prefix''' as [|p3 prefix''''].
        { simpl in Hrest''.
          destruct sub as [|s0 sub'].
          { unfold non_empty in Hne. exfalso. apply Hne. reflexivity. }
          injection Hrest'' as Hs0 Hrest'''.
          subst s0.
          destruct sub' as [|s1 sub''].
          { simpl. lia. }
          injection Hrest''' as Hs1 Hrest''''.
          subst s1.
          destruct sub'' as [|s2 sub'''].
          { simpl. lia. }
          injection Hrest'''' as Hs2 Hrest'''''.
          subst s2.
          destruct sub''' as [|s3 sub''''].
          { simpl. lia. }
          injection Hrest''''' as Hs3 Hrest''''''.
          subst s3.
          destruct sub'''' as [|s4 sub'''''].
          { simpl. lia. }
          destruct suffix; discriminate Hrest''''''. }
        injection Hrest'' as Hp3 Hrest'''.
        subst p3.
        destruct prefix'''' as [|p4 prefix'''''].
        { simpl in Hrest'''.
          destruct sub as [|s0 sub'].
          { unfold non_empty in Hne. exfalso. apply Hne. reflexivity. }
          injection Hrest''' as Hs0 Hrest''''.
          subst s0.
          destruct sub' as [|s1 sub''].
          { simpl. lia. }
          injection Hrest'''' as Hs1 Hrest'''''.
          subst s1.
          destruct sub'' as [|s2 sub'''].
          { simpl. lia. }
          injection Hrest''''' as Hs2 Hrest''''''.
          subst s2.
          destruct sub''' as [|s3 sub''''].
          { simpl. lia. }
          destruct suffix; discriminate Hrest''''''. }
        injection Hrest''' as Hp4 Hrest''''.
        subst p4.
        destruct prefix''''' as [|p5 prefix''''''].
        { simpl in Hrest''''.
          destruct sub as [|s0 sub'].
          { unfold non_empty in Hne. exfalso. apply Hne. reflexivity. }
          injection Hrest'''' as Hs0 Hrest'''''.
          subst s0.
          destruct sub' as [|s1 sub''].
          { simpl. lia. }
          injection Hrest''''' as Hs1 Hrest''''''.
          subst s1.
          destruct sub'' as [|s2 sub'''].
          { simpl. lia. }
          destruct suffix; discriminate Hrest''''''. }
        injection Hrest'''' as Hp5 Hrest'''''.
        subst p5.
        destruct prefix'''''' as [|p6 prefix'''''''].
        { simpl in Hrest'''''.
          destruct sub as [|s0 sub'].
          { unfold non_empty in Hne. exfalso. apply Hne. reflexivity. }
          injection Hrest''''' as Hs0 Hrest''''''.
          subst s0.
          destruct sub' as [|s1 sub''].
          { simpl. lia. }
          destruct suffix; discriminate Hrest''''''. }
        injection Hrest''''' as Hp6 Hrest''''''.
        destruct sub as [|s0 sub'].
        { unfold non_empty in Hne. exfalso. apply Hne. reflexivity. }
        destruct prefix'''''''; discriminate Hrest''''''.
Qed.

Example test_minSubArraySum : minSubArraySum_spec [4; -4; -5; -3; 5; -1; 6] (-12).
Proof.
  unfold minSubArraySum_spec.
  split.
  - discriminate.
  - split.
    + exists [-4; -5; -3].
      split.
      * unfold non_empty. discriminate.
      * split.
        -- unfold is_subarray.
           exists [4], [5; -1; 6].
           reflexivity.
        -- reflexivity.
    + intros sub Hne Hsub.
      apply min_subarray_sum_is_minus12; assumption.
Qed.