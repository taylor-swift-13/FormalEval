Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  规约 1: IsBalanced(s)
  使用 Inductive 定义，其中 count 代表当前未闭合的左括号数。
*)
Inductive IsBalanced_ind : string -> nat -> Prop :=
| IB_nil : IsBalanced_ind "" 0
| IB_lparen : forall t n, IsBalanced_ind t (S n) -> IsBalanced_ind (String lparen t) n
| IB_rparen : forall t n, IsBalanced_ind t n -> IsBalanced_ind (String rparen t) (S n)
| IB_other : forall c t n, c <> lparen -> c <> rparen -> IsBalanced_ind t n -> IsBalanced_ind (String c t) n.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_ind s 0.

(*
  规约 2: IsMinimalBalanced(s)
  s 是平衡的，且不能被分解为两个更小的非空平衡列表。
*)
Definition IsMinimalBalanced (s : string) : Prop :=
  IsBalanced s /\
  ~ (exists s1 s2,
       s1 <> "" /\
       s2 <> "" /\
       s = s1 ++ s2 /\
       IsBalanced s1 /\
       IsBalanced s2).

(*
  辅助函数: 移除列表中的空格
*)
Inductive RemoveSpaces : string -> string -> Prop :=
| RS_nil : RemoveSpaces "" ""
| RS_space : forall t t', RemoveSpaces t t' -> RemoveSpaces (String space t) t'
| RS_char : forall c t t', c <> space -> RemoveSpaces t t' -> RemoveSpaces (String c t) (String c t').

(*
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(*
  辅助函数: 检查字符串中的所有字符是否满足属性 P
*)
Inductive ForallChars (P : ascii -> Prop) : string -> Prop :=
| Forall_nil : ForallChars P ""
| Forall_cons : forall c s, P c -> ForallChars P s -> ForallChars P (String c s).

(*
  前提条件: problem_1_pre
  1. 输入列表中的所有字符都必须是括号或空格。
  2. 输入列表必须是平衡的。
*)
Definition problem_1_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (IsBalanced input).

(*
  最终的程序规约: problem_1_spec(input, output)
  输入和输出都使用 string。
*)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  RemoveSpaces input (String.concat "" output) /\
  (Forall IsMinimalBalanced output).

(* Balanced string lemmas *)
Lemma balanced_empty : IsBalanced "".
Proof.
  unfold IsBalanced. constructor.
Qed.

Lemma balanced_paren : IsBalanced "()".
Proof.
  unfold IsBalanced.
  apply IB_lparen. apply IB_rparen. constructor.
Qed.

Lemma balanced_group1 : IsBalanced "(()())".
Proof.
  unfold IsBalanced.
  apply IB_lparen. apply IB_lparen. apply IB_rparen.
  apply IB_lparen. apply IB_rparen. apply IB_rparen.
  constructor.
Qed.

Lemma balanced_group2 : IsBalanced "((()))".
Proof.
  unfold IsBalanced.
  apply IB_lparen. apply IB_lparen. apply IB_lparen.
  apply IB_rparen. apply IB_rparen. apply IB_rparen.
  constructor.
Qed.

Lemma balanced_group4 : IsBalanced "((())()())".
Proof.
  unfold IsBalanced.
  apply IB_lparen. apply IB_lparen. apply IB_lparen.
  apply IB_rparen. apply IB_rparen. apply IB_lparen.
  apply IB_rparen. apply IB_lparen. apply IB_rparen.
  apply IB_rparen. constructor.
Qed.

(* Inversion lemma for IsBalanced_ind *)
Lemma IsBalanced_ind_lparen_inv : forall s n,
  IsBalanced_ind (String lparen s) n -> IsBalanced_ind s (S n).
Proof.
  intros s n H.
  inversion H; subst.
  - assumption.
  - unfold lparen, rparen in H2. discriminate.
  - exfalso. apply H2. reflexivity.
Qed.

Lemma IsBalanced_ind_rparen_inv : forall s n,
  IsBalanced_ind (String rparen s) (S n) -> IsBalanced_ind s n.
Proof.
  intros s n H.
  inversion H; subst.
  - unfold lparen, rparen in H2. discriminate.
  - assumption.
  - exfalso. apply H3. reflexivity.
Qed.

(* Minimal balanced proofs *)
Lemma minimal_paren : IsMinimalBalanced "()".
Proof.
  unfold IsMinimalBalanced.
  split.
  - exact balanced_paren.
  - intros [s1 [s2 [Hs1ne [Hs2ne [Heq [Hb1 Hb2]]]]]].
    destruct s1 as [|c1 s1']; [contradiction|].
    simpl in Heq. injection Heq as Hc1 Hrest. subst c1.
    destruct s1' as [|c2 s1''].
    + simpl in Hrest. subst s2.
      unfold IsBalanced in Hb1. inversion Hb1; subst.
      * inversion H1.
      * unfold lparen, rparen in H0. discriminate.
      * exfalso. apply H0. reflexivity.
    + simpl in Hrest. injection Hrest as Hc2 Hrest'. subst c2.
      destruct s1'' as [|c3 s1'''].
      * simpl in Hrest'. subst s2. contradiction.
      * simpl in Hrest'. discriminate.
Qed.

Lemma minimal_group1 : IsMinimalBalanced "(()())".
Proof.
  unfold IsMinimalBalanced.
  split.
  - exact balanced_group1.
  - intros [s1 [s2 [Hs1ne [Hs2ne [Heq [Hb1 Hb2]]]]]].
    destruct s1 as [|c1 s1']; [contradiction|].
    simpl in Heq. injection Heq as Hc1 Hrest. subst c1.
    unfold IsBalanced in Hb1.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1' as [|c2 s1'']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc2 Hrest. subst c2.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1'' as [|c3 s1''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc3 Hrest. subst c3.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''' as [|c4 s1'''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc4 Hrest. subst c4.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1'''' as [|c5 s1''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc5 Hrest. subst c5.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''' as [|c6 s1'''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc6 Hrest. subst c6.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''''.
    + simpl in Hrest. subst s2. contradiction.
    + inversion Hb1.
Qed.

Lemma minimal_group2 : IsMinimalBalanced "((()))".
Proof.
  unfold IsMinimalBalanced.
  split.
  - exact balanced_group2.
  - intros [s1 [s2 [Hs1ne [Hs2ne [Heq [Hb1 Hb2]]]]]].
    destruct s1 as [|c1 s1']; [contradiction|].
    simpl in Heq. injection Heq as Hc1 Hrest. subst c1.
    unfold IsBalanced in Hb1.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1' as [|c2 s1'']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc2 Hrest. subst c2.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1'' as [|c3 s1''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc3 Hrest. subst c3.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1''' as [|c4 s1'''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc4 Hrest. subst c4.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1'''' as [|c5 s1''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc5 Hrest. subst c5.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''' as [|c6 s1'''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc6 Hrest. subst c6.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''''.
    + simpl in Hrest. subst s2. contradiction.
    + inversion Hb1.
Qed.

Lemma minimal_group4 : IsMinimalBalanced "((())()())".
Proof.
  unfold IsMinimalBalanced.
  split.
  - exact balanced_group4.
  - intros [s1 [s2 [Hs1ne [Hs2ne [Heq [Hb1 Hb2]]]]]].
    destruct s1 as [|c1 s1']; [contradiction|].
    simpl in Heq. injection Heq as Hc1 Hrest. subst c1.
    unfold IsBalanced in Hb1.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1' as [|c2 s1'']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc2 Hrest. subst c2.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1'' as [|c3 s1''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc3 Hrest. subst c3.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1''' as [|c4 s1'''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc4 Hrest. subst c4.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1'''' as [|c5 s1''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc5 Hrest. subst c5.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''' as [|c6 s1'''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc6 Hrest. subst c6.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1'''''' as [|c7 s1''''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc7 Hrest. subst c7.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''''' as [|c8 s1'''''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc8 Hrest. subst c8.
    apply IsBalanced_ind_lparen_inv in Hb1.
    destruct s1'''''''' as [|c9 s1''''''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc9 Hrest. subst c9.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''''''' as [|c10 s1'''''''''']; [inversion Hb1|].
    simpl in Hrest. injection Hrest as Hc10 Hrest. subst c10.
    apply IsBalanced_ind_rparen_inv in Hb1.
    destruct s1''''''''''.
    + simpl in Hrest. subst s2. contradiction.
    + inversion Hb1.
Qed.

(* RemoveSpaces proof *)
Lemma remove_spaces_test : 
  RemoveSpaces "(()()) ((())) () ((())()())" "(()())((()))()((())()())".
Proof.
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_space.
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_space.
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_space.
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_char; [discriminate|].
  apply RS_nil.
Qed.

Example test_problem_1 :
  problem_1_spec "(()()) ((())) () ((())()())" ["(()())"; "((()))"; "()"; "((())()())"].
Proof.
  unfold problem_1_spec.
  split.
  - simpl. exact remove_spaces_test.
  - repeat constructor.
    + exact minimal_group1.
    + exact minimal_group2.
    + exact minimal_paren.
    + exact minimal_group4.
Qed.