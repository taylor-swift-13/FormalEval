Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Lia.

Import ListNotations.
Open Scope string_scope.

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

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : string) : list string :=
  match S with
  | EmptyString =>
    match current_group with
    | [] => []
    | _ => [string_of_list_ascii (List.rev current_group)]
    end
  | String h t =>
    if ascii_dec h " "%char then
      match current_group with
      | [] => SplitOnSpaces_aux [] t
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

Definition problem_19_pre (input output : string) : Prop := True.

Definition problem_19_spec (input output : string) : Prop :=
    let input_list := SplitOnSpaces input in
    let output_list := SplitOnSpaces output in
    Forall is_valid_word input_list /\
    Permutation input_list output_list /\
    IsSorted output_list.

Example problem_19_test_case_four_two : problem_19_spec "four two" "two four".
Proof.
  unfold problem_19_spec.
  simpl.
  split.
  - constructor.
    + exists 4. apply wtn_four.
    + constructor.
      * exists 2. apply wtn_two.
      * constructor.
  - split.
    + apply perm_swap.
    + unfold IsSorted.
      intros i j Hij Hj s_i s_j n_i n_j Hi Hj' Wi Wj.
      destruct i as [|i'].
      * destruct j as [|j'].
        { exfalso. simpl in Hij. lia. }
        destruct j' as [|j''].
        { simpl in Hi. inversion Hi. subst s_i.
          simpl in Hj'. inversion Hj'. subst s_j.
          inversion Wi; subst.
          inversion Wj; subst.
          simpl. lia. }
        { exfalso. simpl in Hj. lia. }
      * destruct j as [|j'].
        { exfalso. simpl in Hij. lia. }
        { exfalso. simpl in Hj. lia. }
Qed.