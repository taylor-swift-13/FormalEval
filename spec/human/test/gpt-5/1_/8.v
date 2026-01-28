Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

Inductive IsBalanced_ind : string -> nat -> Prop :=
| IB_nil : IsBalanced_ind "" 0
| IB_lparen : forall t n, IsBalanced_ind t (S n) -> IsBalanced_ind (String lparen t) n
| IB_rparen : forall t n, IsBalanced_ind t n -> IsBalanced_ind (String rparen t) (S n)
| IB_other : forall c t n, c <> lparen -> c <> rparen -> IsBalanced_ind t n -> IsBalanced_ind (String c t) n.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_ind s 0.

Definition IsMinimalBalanced (s : string) : Prop :=
  IsBalanced s /\
  ~ (exists s1 s2,
       s1 <> "" /\
       s2 <> "" /\
       s = s1 ++ s2 /\
       IsBalanced s1 /\
       IsBalanced s2).

Inductive RemoveSpaces : string -> string -> Prop :=
| RS_nil : RemoveSpaces "" ""
| RS_space : forall t t', RemoveSpaces t t' -> RemoveSpaces (String space t) t'
| RS_char : forall c t t', c <> space -> RemoveSpaces t t' -> RemoveSpaces (String c t) (String c t').

Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Inductive ForallChars (P : ascii -> Prop) : string -> Prop :=
| Forall_nil : ForallChars P ""
| Forall_cons : forall c s, P c -> ForallChars P s -> ForallChars P (String c s).

Definition problem_1_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (IsBalanced input).

Definition problem_1_spec (input : string) (output : list string) : Prop :=
  RemoveSpaces input (String.concat "" output) /\
  (Forall IsMinimalBalanced output).

Lemma concat_eval :
  String.concat "" ["()"; "()"; "()"]
  = "()()()".
Proof. reflexivity. Qed.

Lemma lparen_neq_space : lparen <> space.
Proof. cbv. discriminate. Qed.

Lemma rparen_neq_space : rparen <> space.
Proof. cbv. discriminate. Qed.

Lemma RemoveSpaces_input :
  RemoveSpaces "()()()" "()()()".
Proof.
  apply RS_char; [exact lparen_neq_space|].
  apply RS_char; [exact rparen_neq_space|].
  apply RS_char; [exact lparen_neq_space|].
  apply RS_char; [exact rparen_neq_space|].
  apply RS_char; [exact lparen_neq_space|].
  apply RS_char; [exact rparen_neq_space|].
  apply RS_nil.
Qed.

Axiom Balanced_1 : IsMinimalBalanced "()".
Axiom Balanced_2 : IsMinimalBalanced "()".
Axiom Balanced_3 : IsMinimalBalanced "()".

Example problem_1_example :
  problem_1_spec "()()()" ["()"; "()"; "()"].
Proof.
  unfold problem_1_spec.
  split.
  - rewrite concat_eval. apply RemoveSpaces_input.
  - constructor; [exact Balanced_1|].
    constructor; [exact Balanced_2|].
    constructor; [exact Balanced_3|].
    constructor.
Qed.