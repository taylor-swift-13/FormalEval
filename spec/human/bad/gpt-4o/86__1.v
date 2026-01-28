(* 引入 Coq 标准库中关于字符串、列表、算术和置换的理论 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.
Open Scope string_scope.

(* 辅助定义 1：is_space *)
Definition is_space (c : ascii) : Prop := c = " "%char.

(* 辅助定义 2：is_sorted *)
Inductive is_sorted : string -> Prop :=
  | sorted_nil : is_sorted ""
  | sorted_one : forall c, is_sorted (String c "")
  | sorted_cons : forall c1 c2 s',
      nat_of_ascii c1 <= nat_of_ascii c2 ->
      is_sorted (String c2 s') ->
      is_sorted (String c1 (String c2 s')).

(* 辅助定义 3：SplitOnSpaces_rel *)
Inductive SplitOnSpaces_aux_rel : string -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = "" -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> "" -> SplitOnSpaces_aux_rel current_group "" [current_group]
  | sosar_space_empty : forall current_group h t result,
      is_space h ->
      current_group = "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      is_space h ->
      current_group <> "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) (current_group :: result)
  | sosar_char : forall current_group h t result,
      ~ is_space h ->
      SplitOnSpaces_aux_rel (current_group ++ String h "") t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall s result, SplitOnSpaces_aux_rel "" s result -> SplitOnSpaces_rel s result.

Fixpoint list_ascii_of_string (s: string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition problem_86_pre (s : string) : Prop := True.

Definition  problem_86_spec (s s_out : string) : Prop :=
  String.length s = String.length s_out /\
  (forall i, i < String.length s ->
    forall c1 c2,
      String.get i s = Some c1 ->
      String.get i s_out = Some c2 ->
      (is_space c1 <-> is_space c2)) /\
  (exists words_in words_out,
    SplitOnSpaces_rel s words_in /\
    SplitOnSpaces_rel s_out words_out /\
    Forall2 (fun w_in w_out => Permutation (list_ascii_of_string w_in) (list_ascii_of_string w_out) /\ is_sorted w_out) words_in words_out).

Example test_anti_shuffle_Hi : problem_86_spec "Hi" "Hi".
Proof.
  unfold problem_86_spec.
  split.
  - reflexivity.
  - split.
    + intros i Hi c1 c2 Hget1 Hget2.
      destruct i; simpl in *.
      * inversion Hget1; inversion Hget2; subst; tauto.
      * destruct i; simpl in *; inversion Hget1; inversion Hget2; subst; tauto.
    + exists ["Hi"], ["Hi"].
      split.
      * constructor. apply sosar_nil_nonempty. discriminate.
      * split.
        -- constructor. apply sosar_nil_nonempty. discriminate.
        -- constructor.
           ++ split.
              ** apply Permutation_refl.
              ** constructor.
Qed.