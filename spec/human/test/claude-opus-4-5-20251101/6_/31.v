Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.
Definition space : ascii := " "%char.

Inductive max_depth_aux_rel : string -> nat -> nat -> nat -> Prop :=
  | mdar_nil : forall current_depth max_seen, max_depth_aux_rel "" current_depth max_seen max_seen
  | mdar_lparen : forall h t current_depth max_seen new_depth new_max result,
      h = lparen ->
      new_depth = S current_depth ->
      new_max = Nat.max max_seen new_depth ->
      max_depth_aux_rel t new_depth new_max result ->
      max_depth_aux_rel (String h t) current_depth max_seen result
  | mdar_rparen : forall h t current_depth max_seen result,
      h = rparen ->
      max_depth_aux_rel t (Nat.pred current_depth) max_seen result ->
      max_depth_aux_rel (String h t) current_depth max_seen result
  | mdar_other : forall h t current_depth max_seen result,
      h <> lparen ->
      h <> rparen ->
      max_depth_aux_rel t current_depth max_seen result ->
      max_depth_aux_rel (String h t) current_depth max_seen result.

Inductive MaxDepth_rel : string -> nat -> Prop :=
  | md_base : forall g result, max_depth_aux_rel g 0 0 result -> MaxDepth_rel g result.


Inductive SplitOnSpaces_aux_rel : list ascii -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = [] -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> [] -> SplitOnSpaces_aux_rel current_group "" [string_of_list_ascii (List.rev current_group)]
  | sosar_space_empty : forall current_group h t result,
      h = space ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = space ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) ((string_of_list_ascii (List.rev current_group)) :: result)
  | sosar_char : forall current_group h t result,
      h <> space ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel [] S result -> SplitOnSpaces_rel S result.

Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Inductive IsBalanced_ind : string -> nat -> Prop :=
| IB_nil : IsBalanced_ind "" 0
| IB_lparen : forall t n, IsBalanced_ind t (S n) -> IsBalanced_ind (String lparen t) n
| IB_rparen : forall t n, IsBalanced_ind t n -> IsBalanced_ind (String rparen t) (S n)
| IB_other : forall c t n, c <> lparen -> c <> rparen -> IsBalanced_ind t n -> IsBalanced_ind (String c t) n.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_ind s 0.


Definition problem_6_pre (input : string) : Prop :=
  (Forall  is_paren_or_space (list_ascii_of_string input)) /\
  (IsBalanced input).

Definition problem_6_spec (input : string) (output : list nat) : Prop :=
  exists groups,
    SplitOnSpaces_rel input groups /\
    length output = length groups /\
    (forall i, i < length groups -> MaxDepth_rel (nth i groups "") (nth i output 0)).

Lemma lparen_neq_space : lparen <> space.
Proof. unfold lparen, space. intro H. inversion H. Qed.

Lemma rparen_neq_space : rparen <> space.
Proof. unfold rparen, space. intro H. inversion H. Qed.

Lemma lparen_neq_rparen : lparen <> rparen.
Proof. unfold lparen, rparen. intro H. inversion H. Qed.

Lemma rparen_neq_lparen : rparen <> lparen.
Proof. unfold lparen, rparen. intro H. inversion H. Qed.

Example problem_6_test :
  problem_6_spec "((((())())))(())(())" [5].
Proof.
  unfold problem_6_spec.
  exists ["((((())())))(())(())"].
  split.
  - apply sos_base.
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply lparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_char. { apply rparen_neq_space. }
    apply sosar_nil_nonempty.
    intro H; inversion H.
  - split.
    + reflexivity.
    + intros i Hi.
      simpl in Hi.
      destruct i as [|i'].
      * simpl.
        apply md_base.
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_lparen; [reflexivity | reflexivity | reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        eapply mdar_rparen; [reflexivity |].
        apply mdar_nil.
      * simpl in Hi. lia.
Qed.