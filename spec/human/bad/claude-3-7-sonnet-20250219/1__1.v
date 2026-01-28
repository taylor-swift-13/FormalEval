(* 引入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.
Definition space : ascii := " "%char.

(* 定义字符串是否平衡的Inductive *)
Inductive IsBalanced_ind : string -> nat -> Prop :=
| IB_nil : IsBalanced_ind "" 0
| IB_lparen : forall t n, IsBalanced_ind t (S n) -> IsBalanced_ind (String lparen t) n
| IB_rparen : forall t n, IsBalanced_ind t n -> IsBalanced_ind (String rparen t) (S n)
| IB_other : forall c t n, c <> lparen -> c <> rparen -> IsBalanced_ind t n -> IsBalanced_ind (String c t) n.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_ind s 0.

(* 定义字符串不可分割成两个非空平衡串 *)
Definition IsMinimalBalanced (s : string) : Prop :=
  IsBalanced s /\
  ~ (exists s1 s2,
       s1 <> "" /\
       s2 <> "" /\
       s = s1 ++ s2 /\
       IsBalanced s1 /\
       IsBalanced s2).

(* 定义去除空格的归约关系 *)
Inductive RemoveSpaces : string -> string -> Prop :=
| RS_nil : RemoveSpaces "" ""
| RS_space : forall t t', RemoveSpaces t t' -> RemoveSpaces (String space t) t'
| RS_char : forall c t t', c <> space -> RemoveSpaces t t' -> RemoveSpaces (String c t) (String c t').

(* 判断字符是否为括号或空格 *)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(* 字符串中所有字符满足P属性 *)
Inductive ForallChars (P : ascii -> Prop) : string -> Prop :=
| Forall_nil : ForallChars P ""
| Forall_cons : forall c s, P c -> ForallChars P s -> ForallChars P (String c s).

(* 输入的前提条件 *)
Definition problem_1_pre (input : string) : Prop :=
  ForallChars is_paren_or_space input /\ IsBalanced input.

(* 规约 *)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  RemoveSpaces input (String.concat "" output) /\ Forall IsMinimalBalanced output.

(* 要证明的测试字串 *)
Definition s1 := "(()())"%string.
Definition s2 := "((()))"%string.
Definition s3 := "()"%string.
Definition s4 := "((())()())"%string.
Definition input := "(()()) ((())) () ((())()())"%string.
Definition output := [s1; s2; s3; s4].

(* 先证明基本平衡性 *)

Lemma s1_balanced : IsBalanced s1.
Proof.
  unfold s1.
  repeat constructor.
Qed.

Lemma s2_balanced : IsBalanced s2.
Proof.
  unfold s2.
  repeat constructor.
Qed.

Lemma s3_balanced : IsBalanced s3.
Proof.
  unfold s3.
  repeat constructor.
Qed.

Lemma s4_balanced : IsBalanced s4.
Proof.
  unfold s4.
  repeat constructor.
Qed.

(* 判断其为最小平衡块 *)

Lemma s_minimal_helper s :
  IsBalanced s ->
  (forall s1 s2, s = s1 ++ s2 -> s1 <> "" -> s2 <> "" -> ~ (IsBalanced s1 /\ IsBalanced s2)) ->
  IsMinimalBalanced s.
Proof.
  intros Hb Hnot.
  split; auto.
  intros [s1 [s2 [Hn1 [Hn2 [Heq [Hb1 Hb2]]]]]].
  apply (Hnot s1 s2 Heq Hn1 Hn2).
  split; assumption.
Qed.

(* 由于手工枚举空间过大，用穷尽法思路断言所有非平凡拆分均不平衡 *)
(* 只需说明结合断言 s1，s2，s3，s4 为最小平衡块 *)

Lemma s1_minimal : IsMinimalBalanced s1.
Proof.
  apply s_minimal_helper.
  - apply s1_balanced.
  - intros s1a s1b Hsplit Hnza Hnzb Hbal.
    unfold s1 in Hsplit.
    (* "(()())" 长度6, 构成3对括号 *)
    (* 破例手工排除 *)
    destruct s1a eqn:Ea, s1b eqn:Eb; try discriminate;
    simpl in Hsplit; inversion Hsplit; subst; try discriminate.
    all: try (inversion Hbal; fail).
Qed.

Lemma s2_minimal : IsMinimalBalanced s2.
Proof.
  apply s_minimal_helper.
  - apply s2_balanced.
  - intros s2a s2b Hsplit Hnza Hnzb Hbal.
    unfold s2 in Hsplit.
    destruct s2a eqn:Ea, s2b eqn:Eb; try discriminate;
    simpl in Hsplit; inversion Hsplit; subst; try discriminate.
    all: try (inversion Hbal; fail).
Qed.

Lemma s3_minimal : IsMinimalBalanced s3.
Proof.
  apply s_minimal_helper.
  - apply s3_balanced.
  - intros s3a s3b Hsplit Hnza Hnzb Hbal.
    unfold s3 in Hsplit.
    destruct s3a eqn:Ea, s3b eqn:Eb; try discriminate;
    simpl in Hsplit; inversion Hsplit; subst; try discriminate.
    all: try (inversion Hbal; fail).
Qed.

Lemma s4_minimal : IsMinimalBalanced s4.
Proof.
  apply s_minimal_helper.
  - apply s4_balanced.
  - intros s4a s4b Hsplit Hnza Hnzb Hbal.
    unfold s4 in Hsplit.
    destruct s4a eqn:Ea, s4b eqn:Eb; try discriminate;
    simpl in Hsplit; inversion Hsplit; subst; try discriminate.
    all: try (inversion Hbal; fail).
Qed.

(* 所有块均为最小平衡块 *)

Lemma Forall_MinimalBalanced_output : Forall IsMinimalBalanced output.
Proof.
  repeat constructor.
  - apply s1_minimal.
  - apply s2_minimal.
  - apply s3_minimal.
  - apply s4_minimal.
  - constructor.
Qed.

(* 去除空格的结合性证明 *)

Lemma RemoveSpaces_app : forall s1 s2 s1' s2',
  RemoveSpaces s1 s1' ->
  RemoveSpaces s2 s2' ->
  RemoveSpaces (s1 ++ s2) (s1' ++ s2').
Proof.
  intros s1 s2.
  revert s2 s1' s2'.
  induction s1; intros s2 s1' s2' Hrem1 Hrem2; simpl.
  - inversion Hrem1; subst. inversion Hrem2; subst. reflexivity.
  - inversion Hrem1; subst.
    + apply RS_space. apply IHs1 with (s1':=s1') (s2':=s2') ; assumption.
    + apply RS_char; auto. apply IHs1 with (s1':=s1') (s2':=s2'); assumption.
Qed.

(* 证明 input 去除空格后等于 concat output *)

Lemma RemoveSpaces_input_output : RemoveSpaces input (String.concat "" output).
Proof.
  unfold input, output, s1, s2, s3, s4.
  (* 分割为串连证明 *)
  repeat (apply RemoveSpaces_app).
  all: try (repeat constructor; discriminate).
  all: try constructor.
  - (* 末尾情况 *)
    constructor.
Qed.

Example test_problem_1 : problem_1_spec input output.
Proof.
  unfold problem_1_spec.
  split.
  - apply RemoveSpaces_input_output.
  - apply Forall_MinimalBalanced_output.
Qed.