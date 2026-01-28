Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope string_scope.

(* Helper function required for the inductive definition *)
Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: s => String c (string_of_list_ascii s)
  end.

(* Provided definitions *)
Inductive WordToNum : string -> nat -> Prop :=
  | wtn_zero  : WordToNum "zero" 0
  | wtn_one   : WordToNum "one" 1
  | wtn_two   : WordToNum "two" 2
  | wtn_three : WordToNum "three" 3
  | wtn_four  : WordToNum "four" 4
  | wtn_five  : WordToNum "five" 5
  | wtn_six   : WordToNum "six" 6
  | wtn_seven : WordToNum "seven" 7
  | wtn_eight : WordToNum "eight" 8
  | wtn_nine  : WordToNum "nine" 9.

Definition is_valid_word (s : string) : Prop :=
  exists n, WordToNum s n.

Definition IsSorted (l : list string) : Prop :=
  forall i j, (i < j)%nat -> j < length l ->
    forall s_i s_j n_i n_j,
      nth i l "" = s_i ->
      nth j l "" = s_j ->
      WordToNum s_i n_i ->
      WordToNum s_j n_j ->
      (n_i <= n_j)%nat.

Inductive SplitOnSpaces_aux_rel : list ascii -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = [] -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> [] -> SplitOnSpaces_aux_rel current_group "" [string_of_list_ascii (List.rev current_group)]
  | sosar_space_empty : forall current_group h t result,
      h = " "%char ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = " "%char ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) ((string_of_list_ascii (List.rev current_group)) :: result)
  | sosar_char : forall current_group h t result,
      h <> " "%char ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel [] S result -> SplitOnSpaces_rel S result.

Definition problem_19_spec (input output : string) : Prop :=
    exists input_list output_list,
    SplitOnSpaces_rel input input_list /\
    SplitOnSpaces_rel output output_list /\
    (*  输入列表中的所有单词都是有效的数字单词 *)
    Forall is_valid_word input_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.

Example test_problem_19_nine : problem_19_spec "nine" "nine".
Proof.
  unfold problem_19_spec.
  exists ["nine"], ["nine"].
  split.
  - (* SplitOnSpaces_rel input *)
    apply sos_base.
    (* Parse "nine" *)
    eapply sosar_char. { intro H; inversion H. }
    eapply sosar_char. { intro H; inversion H. }
    eapply sosar_char. { intro H; inversion H. }
    eapply sosar_char. { intro H; inversion H. }
    apply sosar_nil_nonempty.
    intro H; inversion H.
  - split.
    + (* SplitOnSpaces_rel output *)
      apply sos_base.
      eapply sosar_char. { intro H; inversion H. }
      eapply sosar_char. { intro H; inversion H. }
      eapply sosar_char. { intro H; inversion H. }
      eapply sosar_char. { intro H; inversion H. }
      apply sosar_nil_nonempty.
      intro H; inversion H.
    + split.
      * (* Forall is_valid_word *)
        apply Forall_cons.
        -- exists 9. apply wtn_nine.
        -- apply Forall_nil.
      * split.
        -- (* Permutation *)
           apply Permutation_refl.
        -- (* IsSorted *)
           unfold IsSorted.
           intros i j Hlt Hlen.
           simpl in Hlen.
           lia.
Qed.