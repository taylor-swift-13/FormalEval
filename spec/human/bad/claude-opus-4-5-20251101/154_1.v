(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
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

Example test_cycpattern_check_xyzw_xyw :
  problem_154_spec "xyzw" "xyw" false.
Proof.
  unfold problem_154_spec.
  simpl.
  split.
  - (* false = true -> exists b', ... *)
    intros H. discriminate H.
  - (* exists b', ... -> false = true *)
    intros [b' [Hrot Hsub]].
    unfold is_rotation_of in Hrot.
    unfold is_substring in Hsub.
    destruct Hrot as [p1 [p2 [Hb Hb']]].
    destruct Hsub as [prefix [suffix Hmain]].
    (* lb = [x; y; w] *)
    (* la = [x; y; z; w] *)
    (* Rotations of [x;y;w] are: [x;y;w], [y;w;x], [w;x;y] *)
    (* None of these are substrings of [x;y;z;w] *)
    
    (* Case analysis on p1 *)
    destruct p1 as [|c1 p1'].
    + (* p1 = [] *)
      simpl in Hb. subst p2.
      simpl in Hb'. subst b'.
      (* b' = [x;y;w] *)
      destruct prefix as [|a1 prefix'].
      * (* prefix = [] *)
        simpl in Hmain.
        inversion Hmain as [[H1 H2]].
        destruct suffix as [|s1 suffix'].
        -- simpl in H2. discriminate H2.
        -- inversion H2 as [[H3 H4]].
           destruct suffix' as [|s2 suffix''].
           ++ simpl in H4. discriminate H4.
           ++ inversion H4 as [[H5 H6]].
              (* "w"%char = "z"%char is false *)
              discriminate H5.
      * (* prefix = a1 :: prefix' *)
        simpl in Hmain. inversion Hmain as [[H1 H2]].
        destruct prefix' as [|a2 prefix''].
        -- simpl in H2. inversion H2 as [[H3 H4]].
           destruct suffix as [|s1 suffix'].
           ++ simpl in H4. discriminate H4.
           ++ inversion H4 as [[H5 H6]].
              discriminate H5.
        -- simpl in H2. inversion H2 as [[H3 H4]].
           destruct prefix'' as [|a3 prefix'''].
           ++ simpl in H4. inversion H4 as [[H5 H6]].
              discriminate H5.
           ++ simpl in H4. inversion H4 as [[H5 H6]].
              destruct prefix''' as [|a4 prefix''''].
              ** simpl in H6. discriminate H6.
              ** simpl in H6. discriminate H6.
    + (* p1 = c1 :: p1' *)
      destruct p1' as [|c2 p1''].
      * (* p1 = [c1], so c1 = x, p2 = [y;w] *)
        simpl in Hb. inversion Hb as [[Hc1 Hp2]].
        subst c1 p2.
        simpl in Hb'. subst b'.
        (* b' = [y;w;x] *)
        destruct prefix as [|a1 prefix'].
        -- (* prefix = [] *)
           simpl in Hmain. discriminate Hmain.
        -- (* prefix = a1 :: prefix' *)
           simpl in Hmain. inversion Hmain as [[H1 H2]].
           destruct prefix' as [|a2 prefix''].
           ++ simpl in H2. inversion H2 as [[H3 H4]].
              discriminate H3.
           ++ simpl in H2. inversion H2 as [[H3 H4]].
              destruct prefix'' as [|a3 prefix'''].
              ** simpl in H4. inversion H4 as [[H5 H6]].
                 discriminate H5.
              ** simpl in H4. inversion H4 as [[H5 H6]].
                 destruct prefix''' as [|a4 prefix''''].
                 --- simpl in H6. discriminate H6.
                 --- simpl in H6. discriminate H6.
      * (* p1 = c1 :: c2 :: p1'' *)
        destruct p1'' as [|c3 p1'''].
        -- (* p1 = [c1; c2], so c1 = x, c2 = y, p2 = [w] *)
           simpl in Hb. inversion Hb as [[Hc1 Hrest]].
           inversion Hrest as [[Hc2 Hp2]].
           subst c1 c2 p2.
           simpl in Hb'. subst b'.
           (* b' = [w;x;y] *)
           destruct prefix as [|a1 prefix'].
           ++ (* prefix = [] *)
              simpl in Hmain. discriminate Hmain.
           ++ (* prefix = a1 :: prefix' *)
              simpl in Hmain. inversion Hmain as [[H1 H2]].
              destruct prefix' as [|a2 prefix''].
              ** simpl in H2. inversion H2 as [[H3 H4]].
                 discriminate H3.
              ** simpl in H2. inversion H2 as [[H3 H4]].
                 destruct prefix'' as [|a3 prefix'''].
                 --- simpl in H4. inversion H4 as [[H5 H6]].
                     discriminate H5.
                 --- simpl in H4. inversion H4 as [[H5 H6]].
                     destruct prefix''' as [|a4 prefix''''].
                     +++ simpl in H6. discriminate H6.
                     +++ simpl in H6. discriminate H6.
        -- (* p1 = [c1; c2; c3], so p2 = [] *)
           simpl in Hb. inversion Hb as [[Hc1 Hrest]].
           inversion Hrest as [[Hc2 Hrest2]].
           inversion Hrest2 as [[Hc3 Hp2]].
           subst c1 c2 c3 p2.
           simpl in Hb'. subst b'.
           (* b' = [x;y;w], same as first case *)
           destruct prefix as [|a1 prefix'].
           ++ simpl in Hmain.
              inversion Hmain as [[H1 H2]].
              destruct suffix as [|s1 suffix'].
              ** simpl in H2. discriminate H2.
              ** inversion H2 as [[H3 H4]].
                 destruct suffix' as [|s2 suffix''].
                 --- simpl in H4. discriminate H4.
                 --- inversion H4 as [[H5 H6]].
                     discriminate H5.
           ++ simpl in Hmain. inversion Hmain as [[H1 H2]].
              destruct prefix' as [|a2 prefix''].
              ** simpl in H2. inversion H2 as [[H3 H4]].
                 destruct suffix as [|s1 suffix'].
                 --- simpl in H4. discriminate H4.
                 --- inversion H4 as [[H5 H6]].
                     discriminate H5.
              ** simpl in H2. inversion H2 as [[H3 H4]].
                 destruct prefix'' as [|a3 prefix'''].
                 --- simpl in H4. inversion H4 as [[H5 H6]].
                     discriminate H5.
                 --- simpl in H4. inversion H4 as [[H5 H6]].
                     destruct prefix''' as [|a4 prefix''''].
                     +++ simpl in H6. discriminate H6.
                     +++ simpl in H6. discriminate H6.
Qed.