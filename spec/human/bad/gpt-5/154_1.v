(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* 定义：sub 是 main 的子串 *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* 定义：r 是 b 的一个循环旋转 *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* 任意字符串输入，无额外约束 *)
Definition problem_154_pre (a b : string) : Prop := True.

(* cycpattern_check 函数的程序规约 *)
Definition problem_154_spec (a b : string) (res : bool) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  res = true <-> (exists b', is_rotation_of b' lb /\ is_substring b' la).

(* 辅助引理：旋转保持长度不变 *)
Lemma rotation_length : forall (r b : list ascii),
  is_rotation_of r b -> List.length r = List.length b.
Proof.
  intros r b [p1 [p2 [Hb Hr]]].
  subst r b.
  repeat rewrite List.app_length.
  lia.
Qed.

(* 辅助引理：长度为0的列表是空列表 *)
Lemma length_zero_iff_nil : forall (A : Type) (l : list A),
  List.length l = 0 -> l = [].
Proof.
  intros A l.
  destruct l; simpl; auto.
  intros H; discriminate H.
Qed.

(* 辅助引理：长度为1的列表的构造形式 *)
Lemma length_one_iff_singleton : forall (A : Type) (l : list A),
  List.length l = 1 -> exists x, l = [x].
Proof.
  intros A l.
  destruct l as [|x xs]; simpl; try lia.
  destruct xs as [|y ys]; simpl; try lia.
  intros _; exists x; reflexivity.
Qed.

(* 辅助引理：长度为3的列表的构造形式 *)
Lemma length_three_iff_triple : forall (A : Type) (l : list A),
  List.length l = 3 -> exists x y z, l = x :: y :: z :: [].
Proof.
  intros A l.
  destruct l as [|x xs]; simpl; try lia.
  destruct xs as [|y ys]; simpl; try lia.
  destruct ys as [|z zs]; simpl; try lia.
  intros _; exists x, y, z; reflexivity.
Qed.

(* 引理：b' 是 "xyzw" 的长度为3的子串，则 b' 只能是 "xyz" 或 "yzw" *)
Lemma substring_len3_in_xyzw :
  forall b',
    is_substring b' (list_ascii_of_string "xyzw") ->
    List.length b' = 3 ->
    b' = list_ascii_of_string "xyz" \/
    b' = list_ascii_of_string "yzw".
Proof.
  intros b' Hsub Hlen.
  unfold is_substring in Hsub.
  destruct Hsub as [prefix [suffix Heq]].
  pose proof (f_equal (fun l => List.length l) Heq) as HlenEq.
  simpl in HlenEq. (* length of "xyzw" is 4 *)
  repeat rewrite List.app_length in HlenEq.
  rewrite Hlen in HlenEq.
  (* length prefix + 3 + length suffix = 4 *)
  assert (Hps : List.length prefix + List.length suffix = 1) by lia.
  destruct prefix as [|p ps].
  - (* prefix = [] *)
    simpl in Hps.
    assert (Hls : List.length suffix = 1) by lia.
    apply length_one_iff_singleton in Hls.
    destruct Hls as [s Hsuf].
    apply length_three_iff_triple in Hlen.
    destruct Hlen as [x1 [x2 [x3 Hb3]]].
    subst b'.
    rewrite Hsuf in Heq.
    simpl in Heq.
    (* Compare both sides as 4-element lists *)
    inversion Heq as [H1].
    inversion H1 as [H2].
    inversion H2 as [H3].
    subst.
    left.
    reflexivity.
  - (* prefix = p :: ps *)
    simpl in Hps.
    (* S (length ps) + length suffix = 1 -> length ps = 0 and length suffix = 0 *)
    assert (Hps0 : List.length ps = 0) by lia.
    assert (Hls0 : List.length suffix = 0) by lia.
    apply length_zero_iff_nil in Hps0.
    apply length_zero_iff_nil in Hls0.
    subst ps suffix.
    (* Now Heq: "xyzw" = [p] ++ b' ++ [] -> p :: b' = "xyzw" *)
    simpl in Heq.
    apply length_three_iff_triple in Hlen.
    destruct Hlen as [x1 [x2 [x3 Hb3]]].
    subst b'.
    simpl in Heq.
    inversion Heq as [H1].
    subst p.
    inversion H1 as [H2].
    inversion H2 as [H3].
    subst.
    right.
    reflexivity.
Qed.

(* 证明：不存在将 "xyw" 旋转得到 "xyz" *)
Lemma not_rotation_xyz_from_xyw :
  ~ is_rotation_of (list_ascii_of_string "xyz") (list_ascii_of_string "xyw").
Proof.
  unfold is_rotation_of.
  intros [p1 [p2 [Hb Hr]]].
  simpl in Hb. simpl in Hr.
  destruct p1 as [|a1 p1'].
  - (* p1 = [] *)
    simpl in Hb. subst p2.
    simpl in Hr.
    inversion Hr as [H1].
    inversion H1 as [H2].
    inversion H2.
  - (* p1 = a1 :: p1' *)
    simpl in Hb.
    inversion Hb as [Ha1]. subst a1.
    destruct p1' as [|a2 p1''].
    + (* p1' = [] *)
      simpl in Hb.
      subst.
      simpl in Hr.
      inversion Hr as [H1].
      inversion H1.
    + (* p1' = a2 :: p1'' *)
      simpl in Hb.
      inversion Hb as [Ha2]. subst a2.
      destruct p1'' as [|a3 p1'''].
      * (* p1'' = [] *)
        simpl in Hb. subst.
        simpl in Hr.
        inversion Hr as [H1].
        inversion H1.
      * (* p1'' = a3 :: p1''' *)
        simpl in Hb.
        inversion Hb as [Ha3]. subst a3.
        destruct p1''' as [|a4 p1''''].
        -- simpl in Hb. subst.
           simpl in Hr.
           inversion Hr as [H1].
           inversion H1 as [H2].
           inversion H2.
        -- simpl in Hb. discriminate.
Qed.

(* 证明：不存在将 "xyw" 旋转得到 "yzw" *)
Lemma not_rotation_yzw_from_xyw :
  ~ is_rotation_of (list_ascii_of_string "yzw") (list_ascii_of_string "xyw").
Proof.
  unfold is_rotation_of.
  intros [p1 [p2 [Hb Hr]]].
  simpl in Hb. simpl in Hr.
  destruct p1 as [|a1 p1'].
  - (* p1 = [] *)
    simpl in Hb. subst p2.
    simpl in Hr.
    inversion Hr.
  - (* p1 = a1 :: p1' *)
    simpl in Hb.
    inversion Hb as [Ha1]. subst a1.
    destruct p1' as [|a2 p1''].
    + simpl in Hb. subst.
      simpl in Hr.
      inversion Hr as [H1].
      inversion H1.
    + simpl in Hb.
      inversion Hb as [Ha2]. subst a2.
      destruct p1'' as [|a3 p1'''].
      * simpl in Hb. subst.
        simpl in Hr.
        inversion Hr as [H1].
        inversion H1.
      * simpl in Hb.
        inversion Hb as [Ha3]. subst a3.
        destruct p1''' as [|a4 p1''''].
        -- simpl in Hb. subst.
           simpl in Hr.
           inversion Hr.
        -- simpl in Hb. discriminate.
Qed.

(* 测试用例证明 *)
Example problem_154_example_xyzw_xyw :
  problem_154_spec "xyzw" "xyw" false.
Proof.
  unfold problem_154_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros [b' [Hrot Hsub]].
    pose proof (rotation_length b' (list_ascii_of_string "xyw") Hrot) as Hlen.
    simpl in Hlen.
    assert (Hb'cases :
              b' = list_ascii_of_string "xyz" \/
              b' = list_ascii_of_string "yzw")
      by (apply substring_len3_in_xyzw; assumption; assumption).
    destruct Hb'cases as [Hb_xyz | Hb_yzw].
    + subst b'. exfalso. apply not_rotation_xyz_from_xyw. exact Hrot.
    + subst b'. exfalso. apply not_rotation_yzw_from_xyw. exact Hrot.
Qed.