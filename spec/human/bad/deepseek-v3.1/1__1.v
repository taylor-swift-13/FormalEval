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

Lemma lparen_ne_space : lparen <> space.
Proof. unfold lparen, space; discriminate. Qed.

Lemma rparen_ne_space : rparen <> space.
Proof. unfold rparen, space; discriminate. Qed.

Lemma lparen_ne_rparen : lparen <> rparen.
Proof. unfold lparen, rparen; discriminate. Qed.

Lemma balanced_example1 : IsBalanced "(()())".
Proof.
  unfold IsBalanced.
  apply IB_lparen.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_rparen.
  apply IB_nil.
Qed.

Lemma balanced_example2 : IsBalanced "((()))".
Proof.
  unfold IsBalanced.
  apply IB_lparen.
  apply IB_lparen.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_rparen.
  apply IB_rparen.
  apply IB_nil.
Qed.

Lemma balanced_example3 : IsBalanced "()".
Proof.
  unfold IsBalanced.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_nil.
Qed.

Lemma balanced_example4 : IsBalanced "((())()())".
Proof.
  unfold IsBalanced.
  apply IB_lparen.
  apply IB_lparen.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_rparen.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_lparen.
  apply IB_rparen.
  apply IB_rparen.
  apply IB_nil.
Qed.

Lemma minimal_balanced_example1 : IsMinimalBalanced "(()())".
Proof.
  unfold IsMinimalBalanced.
  split.
  - apply balanced_example1.
  - unfold not.
    intros [s1 [s2 [H1 [H2 [H3 H4]]]]].
    destruct s1 as [|c1 s1'].
    + contradiction H1; reflexivity.
    + destruct s2 as [|c2 s2'].
      * contradiction H2; reflexivity.
      * inversion H3.
Qed.

Lemma minimal_balanced_example2 : IsMinimalBalanced "((()))".
Proof.
  unfold IsMinimalBalanced.
  split.
  - apply balanced_example2.
  - unfold not.
    intros [s1 [s2 [H1 [H2 [H3 H4]]]]].
    destruct s1 as [|c1 s1'].
    + contradiction H1; reflexivity.
    + destruct s2 as [|c2 s2'].
      * contradiction H2; reflexivity.
      * inversion H3.
Qed.

Lemma minimal_balanced_example3 : IsMinimalBalanced "()".
Proof.
  unfold IsMinimalBalanced.
  split.
  - apply balanced_example3.
  - unfold not.
    intros [s1 [s2 [H1 [H2 [H3 H4]]]]].
    destruct s1 as [|c1 s1'].
    + contradiction H1; reflexivity.
    + destruct s2 as [|c2 s2'].
      * contradiction H2; reflexivity.
      * inversion H3.
Qed.

Lemma minimal_balanced_example4 : IsMinimalBalanced "((())()())".
Proof.
  unfold IsMinimalBalanced.
  split.
  - apply balanced_example4.
  - unfold not.
    intros [s1 [s2 [H1 [H2 [H3 H4]]]]].
    destruct s1 as [|c1 s1'].
    + contradiction H1; reflexivity.
    + destruct s2 as [|c2 s2'].
      * contradiction H2; reflexivity.
      * inversion H3.
Qed.

Lemma remove_spaces_example : RemoveSpaces "(()()) ((())) () ((())()())" "(()())((()))()((())()())".
Proof.
  simpl.
  repeat (apply RS_char; [discriminate |]).
  apply RS_space.
  repeat (apply RS_char; [discriminate |]).
  apply RS_space.
  repeat (apply RS_char; [discriminate |]).
  apply RS_space.
  repeat (apply RS_char; [discriminate |]).
  apply RS_nil.
Qed.

Example test_case_proof :
  problem_1_spec "(()()) ((())) () ((())()())" ["(()())"; "((()))"; "()"; "((())()())"].
Proof.
  unfold problem_1_spec.
  split.
  - (* Prove RemoveSpaces *)
    apply remove_spaces_example.
  - (* Prove Forall IsMinimalBalanced *)
    repeat constructor.
    + apply minimal_balanced_example1.
    + apply minimal_balanced_example2.
    + apply minimal_balanced_example3.
    + apply minimal_balanced_example4.
Qed.