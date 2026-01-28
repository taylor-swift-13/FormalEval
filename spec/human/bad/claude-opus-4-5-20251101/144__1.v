Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* 将单个ASCII字符转换为数字 (0-9)，假设输入合法 *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

(* 辅助关系：将list ascii转换为自然数 *)
Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
| latn_nil : list_ascii_to_nat_rel [] 0
| latn_cons : forall c l n,
    list_ascii_to_nat_rel l n ->
    list_ascii_to_nat_rel (l ++ [c]) (n * 10 + char_to_digit c).

Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    list_ascii_to_nat_rel num_s num /\
    list_ascii_to_nat_rel den_s den.

Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if (product_num mod product_den) =? 0
             then true
             else false.

(* Lemma for parsing single digit "1" -> 1 *)
Lemma parse_single_1 : list_ascii_to_nat_rel ["1"%char] 1.
Proof.
  change ["1"%char] with ([] ++ ["1"%char]).
  replace 1 with (0 * 10 + char_to_digit "1"%char) by reflexivity.
  apply latn_cons.
  apply latn_nil.
Qed.

(* Lemma for parsing single digit "5" -> 5 *)
Lemma parse_single_5 : list_ascii_to_nat_rel ["5"%char] 5.
Proof.
  change ["5"%char] with ([] ++ ["5"%char]).
  replace 5 with (0 * 10 + char_to_digit "5"%char) by reflexivity.
  apply latn_cons.
  apply latn_nil.
Qed.

(* Main test case: simplify("1/5", "5/1") = true *)
Example test_simplify_1_5_5_1 : problem_144_spec "1/5" "5/1" true.
Proof.
  unfold problem_144_spec.
  exists 1, 5, 5, 1.
  split.
  - (* Parse "1/5" *)
    unfold Parse_Fraction.
    exists ["1"%char], ["5"%char].
    split.
    + reflexivity.
    + split.
      * exact parse_single_1.
      * exact parse_single_5.
  - split.
    + (* Parse "5/1" *)
      unfold Parse_Fraction.
      exists ["5"%char], ["1"%char].
      split.
      * reflexivity.
      * split.
        -- exact parse_single_5.
        -- exact parse_single_1.
    + split. { lia. }
      split. { lia. }
      split. { lia. }
      split. { lia. }
      (* output = true *)
      reflexivity.
Qed.