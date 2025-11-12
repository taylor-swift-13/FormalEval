(* def simplify(x, n):
Your task is to implement a function that will simplify the expression
x * n. The function returns True if x * n evaluates to a whole number and False
otherwise. Both x and n, are string representation of a fraction, and have the following format,
<numerator>/<denominator> where both numerator and denominator are positive whole numbers.

You can assume that x, and n are valid fractions, and do not have zero as denominator.

simplify("1/5", "5/1") = True
simplify("1/6", "2/1") = False
simplify("7/10", "10/2") = False *)
(* 导入所需的Coq库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

Inductive list_ascii_to_nat_aux_rel : list ascii -> nat -> nat -> Prop :=
  | latnar_nil : forall acc, list_ascii_to_nat_aux_rel [] acc acc
  | latnar_cons : forall c l' acc acc' result,
      acc' = acc * 10 + char_to_digit c ->
      list_ascii_to_nat_aux_rel l' acc' result ->
      list_ascii_to_nat_aux_rel (c :: l') acc result.

Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
  | latnr_base : forall l n, list_ascii_to_nat_aux_rel l 0 n -> list_ascii_to_nat_rel l n.

Inductive find_slash_rel : list ascii -> option (list ascii * list ascii) -> Prop :=
  | fsr_nil : find_slash_rel [] None
  | fsr_slash : forall rest, find_slash_rel ("/"%char :: rest) (Some ([], rest))
  | fsr_char : forall h t num_s den_s,
      find_slash_rel t (Some (num_s, den_s)) ->
      find_slash_rel (h :: t) (Some (h :: num_s, den_s))
  | fsr_no_slash : forall h t,
      find_slash_rel t None ->
      find_slash_rel (h :: t) None.

Inductive parse_fraction_rel : list ascii -> option (nat * nat) -> Prop :=
  | pfr_none : forall s, find_slash_rel s None -> parse_fraction_rel s None
  | pfr_some : forall s num_s den_s num den,
      find_slash_rel s (Some (num_s, den_s)) ->
      list_ascii_to_nat_rel (rev num_s) num ->
      list_ascii_to_nat_rel den_s den ->
      parse_fraction_rel s (Some (num, den)).



Definition simplify_spec (x n : list ascii) (output : bool) : Prop :=
  (exists num_x den_x num_n den_n product_num product_den,
     parse_fraction_rel x (Some (num_x, den_x)) /\
     parse_fraction_rel n (Some (num_n, den_n)) /\
     product_num = num_x * num_n /\
     product_den = den_x * den_n /\
     (product_num mod product_den = 0) /\
     output = true) \/
  (exists num_x den_x num_n den_n product_num product_den,
     parse_fraction_rel x (Some (num_x, den_x)) /\
     parse_fraction_rel n (Some (num_n, den_n)) /\
     product_num = num_x * num_n /\
     product_den = den_x * den_n /\
     (product_num mod product_den <> 0) /\
     output = false) \/
  ((parse_fraction_rel x None \/ parse_fraction_rel n None) /\
   output = false).
