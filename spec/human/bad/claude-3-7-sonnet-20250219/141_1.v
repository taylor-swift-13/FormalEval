Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Import Nat.

Open Scope string_scope.
Open Scope list_scope.

(* Correct is_digit_bool definition: use ascii constants, not strings *)
Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

Definition problem_141_spec (file_name_str : string) (result : string) : Prop :=
  let file_name := list_ascii_of_string file_name_str in
  let is_valid :=
    (length (filter is_digit_bool file_name) <= 3) /\
    (exists prefix suffix,
       file_name = prefix ++ "."%char :: suffix /\
       ~ In "."%char (prefix ++ suffix) /\
       (exists first_char rest_prefix,
          prefix = first_char :: rest_prefix /\ is_alpha first_char) /\
       (suffix = ("t"::"x"::"t"::[])%char \/
        suffix = ("e"::"x"::"e"::[])%char \/
        suffix = ("d"::"l"::"l"::[])%char))
  in
  (is_valid /\ result = "Yes") \/
  (~is_valid /\ result = "No").

(* Auxiliary lemma: is_alpha holds for 'e' *)
Lemma is_alpha_e : is_alpha "e"%char.
Proof.
  unfold is_alpha.
  left; split; reflexivity.
Qed.

Example problem_141_example_proof :
  problem_141_spec "example.txt" "Yes".
Proof.
  unfold problem_141_spec.
  simpl.

  set (file_name :=
    ["e"; "x"; "a"; "m"; "p"; "l"; "e"; "."; "t"; "x"; "t"]%char).

  (* Count digits in file_name: zero digits *)
  assert (length (filter is_digit_bool file_name) = 0).
  {
    subst file_name.
    simpl.
    repeat (
      unfold is_digit_bool;
      simpl;
      let n := eval compute in (nat_of_ascii _) in
      (* 0x30 to 0x39 = '0'..'9' : decimal 48..57 *)
      (* show each character has nat_of_ascii outside [48..57] *)
      match goal with
      | |- context[is_digit_bool ?c] =>
        let v := (eval compute in (nat_of_ascii c)) in
        assert (v < 48 \/ v > 57) by lia;
        destruct H; rewrite ?Nat.leb_gt; try lia; simpl; reflexivity
      end).
  }
  rewrite H.
  assert (0 <= 3) by lia.
  clear H.

  split.
  - assumption.
  - exists ["e"; "x"; "a"; "m"; "p"; "l"; "e"],
           ["t"; "x"; "t"].
    repeat split.
    + reflexivity.
    + unfold not; intros Hin.
      apply in_app_or in Hin.
      destruct Hin; simpl in *; discriminate.
    + exists "e"%char, ["x"; "a"; "m"; "p"; "l"; "e"].
      split; [reflexivity|].
      exact is_alpha_e.
    + left; reflexivity.
Qed.