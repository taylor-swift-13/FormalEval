(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

(* 定义一个函数来计算整数列表的和 *)
Definition list_sum (l : list Z) : Z :=
  fold_left Z.add l 0.

(* nums 非空 *)
Definition problem_114_pre (nums : list Z) : Prop := nums <> [].

(* 定义一个规约来描述最小子数组和的属性 *)
Definition problem_114_spec (nums : list Z) (min_sum : Z) : Prop :=
  (* 1. 存在性 (Existence): 必须存在一个非空子数组，其和等于 min_sum *)
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    list_sum sub_array = min_sum)
  /\
  (* 2. 最小性 (Minimality): 对于所有非空的子数组，它们的和都必须大于或等于 min_sum *)
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    min_sum <= list_sum sub_array).

(* Helper lemma for fold_left with addition *)
Lemma fold_left_add_acc : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l; intros; simpl.
  - lia.
  - rewrite IHl. rewrite (IHl a). lia.
Qed.

(* Lemma: if prefix ++ sub ++ suffix = nums, then sub is determined by the decomposition *)
Lemma app_decompose : forall {A : Type} (l1 l2 l3 l4 : list A) (x : A),
  l1 ++ [x] ++ l2 = l3 ++ l4 ->
  (exists l1', l3 = l1 ++ [x] ++ l1' /\ l2 = l1' ++ l4) \/
  (exists l4', l4 = l4' ++ [x] ++ l2 /\ l1 = l3 ++ l4') \/
  (l1 = l3 /\ [x] ++ l2 = l4).
Proof.
  intros A l1.
  induction l1; intros; simpl in *.
  - right. right. split; auto.
  - destruct l3; simpl in *.
    + right. left. exists []. simpl. inversion H. auto.
    + inversion H. subst.
      destruct (IHl1 l2 l3 l4 x H2) as [[l1' [H3 H4]] | [[l4' [H3 H4]] | [H3 H4]]].
      * left. exists l1'. split; auto. rewrite H3. auto.
      * right. left. exists (a0 :: l4'). simpl. split; auto. rewrite H4. auto.
      * right. right. split; auto. rewrite H3. auto.
Qed.

(* Main example proof *)
Example problem_114_test1 :
  problem_114_spec [2%Z; 3%Z; 4%Z; 1%Z; 2%Z; 4%Z] 1%Z.
Proof.
  unfold problem_114_spec.
  split.
  - (* Existence: there exists a subarray with sum = 1 *)
    exists [1%Z].
    split.
    + discriminate.
    + split.
      * exists [2%Z; 3%Z; 4%Z], [2%Z; 4%Z].
        reflexivity.
      * unfold list_sum. simpl. reflexivity.
  - (* Minimality: all non-empty subarrays have sum >= 1 *)
    intros sub_array Hne [prefix [suffix Heq]].
    (* All elements are positive, so minimum is the smallest element = 1 *)
    (* We prove by case analysis on what sub_array could be *)
    destruct sub_array as [|a rest]; [contradiction|].
    (* sub_array = a :: rest *)
    (* The subarray must be a contiguous part of [2; 3; 4; 1; 2; 4] *)
    destruct prefix as [|p0 prefix'].
    + (* prefix = [] *)
      simpl in Heq. injection Heq as Ha Hrest.
      subst a.
      (* sub_array starts with 2 *)
      unfold list_sum. simpl.
      destruct rest as [|r0 rest'].
      * simpl. lia.
      * rewrite fold_left_add_acc. 
        assert (fold_left Z.add rest' 0 >= 0 \/ fold_left Z.add rest' 0 < 0) by lia.
        injection Hrest as Hr0 Hrest'.
        subst r0.
        destruct rest' as [|r1 rest''].
        -- simpl. lia.
        -- injection Hrest' as Hr1 Hrest''.
           subst r1.
           destruct rest'' as [|r2 rest'''].
           ++ simpl. lia.
           ++ injection Hrest'' as Hr2 Hrest'''.
              subst r2.
              destruct rest''' as [|r3 rest''''].
              ** simpl. lia.
              ** injection Hrest''' as Hr3 Hrest''''.
                 subst r3.
                 destruct rest'''' as [|r4 rest'''''].
                 --- simpl. lia.
                 --- injection Hrest'''' as Hr4 Hrest'''''.
                     subst r4.
                     destruct rest'''''; destruct suffix; simpl in Hrest'''''; try discriminate.
                     simpl. lia.
    + (* prefix = p0 :: prefix' *)
      injection Heq as Hp0 Hrest.
      subst p0.
      destruct prefix' as [|p1 prefix''].
      * (* prefix = [2] *)
        simpl in Hrest. injection Hrest as Ha Hrest'.
        subst a.
        unfold list_sum. simpl.
        destruct rest as [|r0 rest'].
        -- simpl. lia.
        -- rewrite fold_left_add_acc.
           injection Hrest' as Hr0 Hrest''.
           subst r0.
           destruct rest' as [|r1 rest''].
           ++ simpl. lia.
           ++ injection Hrest'' as Hr1 Hrest'''.
              subst r1.
              destruct rest'' as [|r2 rest'''].
              ** simpl. lia.
              ** injection Hrest''' as Hr2 Hrest''''.
                 subst r2.
                 destruct rest''' as [|r3 rest''''].
                 --- simpl. lia.
                 --- injection Hrest'''' as Hr3 Hrest'''''.
                     subst r3.
                     destruct rest''''; destruct suffix; simpl in Hrest'''''; try discriminate.
                     simpl. lia.
      * (* prefix = [2; p1; ...] *)
        injection Hrest as Hp1 Hrest'.
        subst p1.
        destruct prefix'' as [|p2 prefix'''].
        -- (* prefix = [2; 3] *)
           simpl in Hrest'. injection Hrest' as Ha Hrest''.
           subst a.
           unfold list_sum. simpl.
           destruct rest as [|r0 rest'].
           ++ simpl. lia.
           ++ rewrite fold_left_add_acc.
              injection Hrest'' as Hr0 Hrest'''.
              subst r0.
              destruct rest' as [|r1 rest''].
              ** simpl. lia.
              ** injection Hrest''' as Hr1 Hrest''''.
                 subst r1.
                 destruct rest'' as [|r2 rest'''].
                 --- simpl. lia.
                 --- injection Hrest'''' as Hr2 Hrest'''''.
                     subst r2.
                     destruct rest'''; destruct suffix; simpl in Hrest'''''; try discriminate.
                     simpl. lia.
        -- injection Hrest' as Hp2 Hrest''.
           subst p2.
           destruct prefix''' as [|p3 prefix''''].
           ++ (* prefix = [2; 3; 4] *)
              simpl in Hrest''. injection Hrest'' as Ha Hrest'''.
              subst a.
              unfold list_sum. simpl.
              destruct rest as [|r0 rest'].
              ** simpl. lia.
              ** rewrite fold_left_add_acc.
                 injection Hrest''' as Hr0 Hrest''''.
                 subst r0.
                 destruct rest' as [|r1 rest''].
                 --- simpl. lia.
                 --- injection Hrest'''' as Hr1 Hrest'''''.
                     subst r1.
                     destruct rest''; destruct suffix; simpl in Hrest'''''; try discriminate.
                     simpl. lia.
           ++ injection Hrest'' as Hp3 Hrest'''.
              subst p3.
              destruct prefix'''' as [|p4 prefix'''''].
              ** (* prefix = [2; 3; 4; 1] *)
                 simpl in Hrest'''. injection Hrest''' as Ha Hrest''''.
                 subst a.
                 unfold list_sum. simpl.
                 destruct rest as [|r0 rest'].
                 --- simpl. lia.
                 --- rewrite fold_left_add_acc.
                     injection Hrest'''' as Hr0 Hrest'''''.
                     subst r0.
                     destruct rest'; destruct suffix; simpl in Hrest'''''; try discriminate.
                     simpl. lia.
              ** injection Hrest''' as Hp4 Hrest''''.
                 subst p4.
                 destruct prefix'''''.
                 --- (* prefix = [2; 3; 4; 1; 2] *)
                     simpl in Hrest''''. injection Hrest'''' as Ha Hrest'''''.
                     subst a.
                     unfold list_sum. simpl.
                     destruct rest; destruct suffix; simpl in Hrest'''''; try discriminate.
                     simpl. lia.
                 --- simpl in Hrest''''. discriminate.
Qed.