Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Inductive is_odd_digit : ascii -> Prop :=
| iod_1 : is_odd_digit "1"%char
| iod_3 : is_odd_digit "3"%char
| iod_5 : is_odd_digit "5"%char
| iod_7 : is_odd_digit "7"%char
| iod_9 : is_odd_digit "9"%char.

Inductive count_odd_digits_rel : string -> nat -> Prop :=
| codr_empty : count_odd_digits_rel "" 0%nat
| codr_odd : forall c s n, is_odd_digit c -> count_odd_digits_rel s n ->
    count_odd_digits_rel (String c s) (S n)
| codr_not_odd : forall c s n, ~ is_odd_digit c -> count_odd_digits_rel s n ->
    count_odd_digits_rel (String c s) n.

Inductive replace_char_with_string_rel : ascii -> string -> string -> string -> Prop :=
| rcr_empty : forall t r, replace_char_with_string_rel t r "" ""
| rcr_match : forall t r s s', replace_char_with_string_rel t r s s' ->
   replace_char_with_string_rel t r (String t s) (r ++ s')
| rcr_no_match : forall t r c s s', c <> t -> replace_char_with_string_rel t r s s' ->
   replace_char_with_string_rel t r (String c s) (String c s').

(* 辅助关系：将 nat 转换为 string (逆序) *)
Inductive nat_to_string_aux_rel : nat -> string -> Prop :=
| ntsar_zero : nat_to_string_aux_rel 0 ""
| ntsar_step : forall m s, m <> 0 ->
    nat_to_string_aux_rel (m / 10) s ->
    nat_to_string_aux_rel m (String (ascii_of_nat (48 + (m mod 10))) s).

(* 辅助关系：反转字符串 *)
Inductive rev_string_rel : string -> string -> Prop :=
| rsr_empty : rev_string_rel "" ""
| rsr_cons : forall c s s', rev_string_rel s s' ->
    rev_string_rel (String c s) (s' ++ String c "").

(* 辅助关系：将 nat 转换为 string *)
Inductive nat_to_string_rel : nat -> string -> Prop :=
| ntsr_zero : nat_to_string_rel 0 "0"
| ntsr_pos : forall n s s_rev, n <> 0 ->
    nat_to_string_aux_rel n s ->
    rev_string_rel s s_rev ->
    nat_to_string_rel n s_rev.

(* 固定模板：将其中的字符 'i' 替换为计数字符 *)
Definition odd_count_template : string :=
    "the number of odd elements in the string i of the input.".

Inductive process_string_rel : string -> string -> Prop :=
| psr_build : forall s cnt cnt_str res,
    count_odd_digits_rel s cnt ->
    nat_to_string_rel cnt cnt_str ->
    replace_char_with_string_rel "i"%char cnt_str odd_count_template res ->
    process_string_rel s res.

Inductive odd_count_rel : list string -> list string -> Prop :=
| ocr_nil : odd_count_rel nil nil
| ocr_cons : forall h t h' t', process_string_rel h h' ->
    odd_count_rel t t' ->
    odd_count_rel (h :: t) (h' :: t').

(* 每个字符串只包含数字字符 *)
Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    let fix all_digits (t : string) : Prop :=
      match t with
      | EmptyString => True
      | String ch rest =>
          let n := nat_of_ascii ch in (48 <= n /\ n <= 57) /\ all_digits rest
      end in all_digits s) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  odd_count_rel input output.

(* Tactics to automate the proof steps *)

Ltac solve_count :=
  repeat (
    apply codr_empty ||
    (apply codr_odd; [ constructor | ]) ||
    (apply codr_not_odd; [ let H := fresh in intro H; inversion H | ])
  ).

Ltac solve_replace :=
  repeat (
    apply rcr_empty ||
    apply rcr_match ||
    (apply rcr_no_match; [ let H := fresh in intro H; inversion H | ])
  ).

Example test_problem_113 :
  problem_113_spec ["1234567"] ["the number of odd elements 4n the str4ng 4 of the 4nput."].
Proof.
  unfold problem_113_spec.
  apply ocr_cons.
  - (* Process the first string "1234567" *)
    eapply psr_build.
    + (* Step 1: Count odd digits. Should be 4. *)
      solve_count.
    + (* Step 2: Convert count 4 to string "4". *)
      eapply ntsr_pos.
      * (* 4 <> 0 *)
        intro H; inversion H.
      * (* Build aux string *)
        eapply ntsar_step.
        { intro H; inversion H. }
        { simpl. apply ntsar_zero. }
      * (* Reverse string *)
        simpl. apply rsr_cons. apply rsr_empty.
    + (* Step 3: Replace 'i' in template with "4". *)
      unfold odd_count_template.
      solve_replace.
  - (* Tail of the list is nil *)
    apply ocr_nil.
Qed.