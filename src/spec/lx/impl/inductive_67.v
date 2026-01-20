(* HumanEval 67 - Inductive Spec *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.ZArith.ZArith.
Open Scope Z_scope.

Inductive is_digit : ascii -> Prop :=
| id_0 : is_digit "0"%char
| id_1 : is_digit "1"%char
| id_2 : is_digit "2"%char
| id_3 : is_digit "3"%char
| id_4 : is_digit "4"%char
| id_5 : is_digit "5"%char
| id_6 : is_digit "6"%char
| id_7 : is_digit "7"%char
| id_8 : is_digit "8"%char
| id_9 : is_digit "9"%char.

Inductive digit_val_rel : ascii -> Z -> Prop :=
| dvr_0 : digit_val_rel "0"%char 0%Z
| dvr_1 : digit_val_rel "1"%char 1%Z
| dvr_2 : digit_val_rel "2"%char 2%Z
| dvr_3 : digit_val_rel "3"%char 3%Z
| dvr_4 : digit_val_rel "4"%char 4%Z
| dvr_5 : digit_val_rel "5"%char 5%Z
| dvr_6 : digit_val_rel "6"%char 6%Z
| dvr_7 : digit_val_rel "7"%char 7%Z
| dvr_8 : digit_val_rel "8"%char 8%Z
| dvr_9 : digit_val_rel "9"%char 9%Z.

Inductive drop_prefix_rel : string -> string -> option string -> Prop :=
| dpr_empty : forall s, drop_prefix_rel "" s (Some s)
| dpr_match : forall c1 p' c2 s' res, Ascii.eqb c1 c2 = true ->
   drop_prefix_rel p' s' res ->
   drop_prefix_rel (String c1 p') (String c2 s') res
| dpr_no_match : forall c1 p' c2 s', Ascii.eqb c1 c2 = false ->
   drop_prefix_rel (String c1 p') (String c2 s') None.

Inductive read_number_acc_rel : string -> Z -> bool -> option (Z * string) -> Prop :=
| rnar_seen_empty : forall acc, read_number_acc_rel EmptyString acc true (Some (acc, EmptyString))
| rnar_seen_char : forall acc c rest n rest2, ~ is_digit c ->
   read_number_acc_rel rest n true (Some (n, rest2)) ->
   read_number_acc_rel (String c rest) acc true (Some (acc, String c rest))
| rnar_digit : forall c rest acc seen res d, is_digit c -> digit_val_rel c d ->
   read_number_acc_rel rest (10 * acc + d) true res ->
   read_number_acc_rel (String c rest) acc seen res
| rnar_unseen : forall c rest, ~ is_digit c ->
   read_number_acc_rel (String c rest) 0 false None.

Inductive read_number_rel : string -> option (Z * string) -> Prop :=
| rnr_empty : read_number_rel "" None
| rnr_no_digit : forall c s, ~ is_digit c -> read_number_rel (String c s) None
| rnr_digit : forall c s n rest d, is_digit c -> digit_val_rel c d ->
   read_number_acc_rel s d true (Some (n, rest)) ->
   read_number_rel (String c s) (Some (n, rest)).

Inductive parse_apples_oranges_rel : string -> option (Z * Z) -> Prop :=
| paor_success : forall s a o s1 s2 s3 s4,
   read_number_rel s (Some (a, s1)) ->
   drop_prefix_rel " apples and "%string s1 (Some s2) ->
   read_number_rel s2 (Some (o, s3)) ->
   drop_prefix_rel " oranges"%string s3 (Some s4) ->
   parse_apples_oranges_rel s (Some (a, o))
| paor_fail : forall s, ~ (exists a o s1 s2 s3 s4,
   read_number_rel s (Some (a, s1)) /\
   drop_prefix_rel " apples and "%string s1 (Some s2) /\
   read_number_rel s2 (Some (o, s3)) /\
   drop_prefix_rel " oranges"%string s3 (Some s4)) ->
   parse_apples_oranges_rel s None.

Definition fruit_distribution_spec (s : string) (n : Z) (output : Z) : Prop :=
  (exists apples oranges, parse_apples_oranges_rel s (Some (apples, oranges)) /\
    output = n - (apples + oranges)) \/
  (parse_apples_oranges_rel s None /\ output = n).

