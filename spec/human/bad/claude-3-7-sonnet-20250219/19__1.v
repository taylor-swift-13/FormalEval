Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope string_scope.

(* Helper function: convert list ascii to string *)
Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => ""
  | h :: t => String h (string_of_list_ascii t)
  end.

Inductive SplitOnSpaces_aux_rel : list ascii -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group,
      current_group = [] ->
      SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group,
      current_group <> [] ->
      SplitOnSpaces_aux_rel current_group "" [string_of_list_ascii (List.rev current_group)]
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
  | sos_base : forall S result,
      SplitOnSpaces_aux_rel [] S result ->
      SplitOnSpaces_rel S result.

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

Definition problem_19_spec (input output : string) : Prop :=
  exists input_list output_list,
    SplitOnSpaces_rel input input_list /\
    SplitOnSpaces_rel output output_list /\
    Forall is_valid_word input_list /\
    Permutation input_list output_list /\
    IsSorted output_list.

Example problem_19_empty_string :
  problem_19_spec "" "".
Proof.
  unfold problem_19_spec.
  eexists [], [].
  repeat split.
  - (* SplitOnSpaces_rel input [] *)
    constructor.
    apply sosar_nil_empty.
    reflexivity.
  - (* SplitOnSpaces_rel output [] *)
    constructor.
    apply sosar_nil_empty.
    reflexivity.
  - (* Forall is_valid_word [] *)
    simpl. constructor.
  - (* Permutation [] [] *)
    apply Permutation_refl.
  - (* IsSorted [] *)
    unfold IsSorted.
    intros i j Hlt Hj s_i s_j n_i n_j.
    simpl in Hj.
    lia.
Qed.