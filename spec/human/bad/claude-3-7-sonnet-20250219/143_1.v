Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool Coq.Arith.PeanoNat.
Import ListNotations.

(* Definitions from the specification: *)

Fixpoint has_divisor_from (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => false
  | S d' =>
    if (n mod d =? 0)%nat then true else has_divisor_from n d'
  end.

Definition is_prime_bool (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => negb (has_divisor_from n (n - 1))
  end.

Fixpoint split_words_aux (cur rest : list ascii) : list (list ascii) :=
  let space := " "%char in
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Ascii.eqb h space then
        match cur with
        | [] => split_words_aux [] t
        | _ => (rev cur) :: split_words_aux [] t
        end
      else
        split_words_aux (h :: cur) t
  end.

Definition split_words (s : list ascii) := split_words_aux [] s.

Fixpoint join_words (ws : list (list ascii)) : list ascii :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest => w ++ (" "%char :: nil) ++ join_words rest
  end.

Definition words_in_sentence_impl (sentence : string) : string :=
  let words := split_words (list_ascii_of_string sentence) in
  let sel := List.filter (fun w => is_prime_bool (length w)) words in
  string_of_list_ascii (join_words sel).

(* Lemma: string_of_list_ascii and list_ascii_of_string are inverse *)
Lemma string_list_ascii_inverse : forall s,
  string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  intros s.
  unfold string_of_list_ascii, list_ascii_of_string.
  induction s as [| c s IH].
  - simpl; reflexivity.
  - simpl.
    f_equal.
    apply IH.
Qed.

(* Test case proof *)

Example test_words_in_sentence_This_is :
  words_in_sentence_impl "This is a test" = "is".
Proof.
  unfold words_in_sentence_impl.

  (* Compute split_words (list_ascii_of_string "This is a test") *)
  (* The ascii list of "This is a test" is: *)
  (* [ "T"; "h"; "i"; "s"; " "; "i"; "s"; " "; "a"; " "; "t"; "e"; "s"; "t" ] *)
  set (input_list := list_ascii_of_string "This is a test").

  (* We compute the split_words_aux [] input_list *)
  assert (Hsplit: split_words input_list =
   [list_ascii_of_string "This";
    list_ascii_of_string "is";
    list_ascii_of_string "a";
    list_ascii_of_string "test"]).
  {
    unfold split_words, input_list.
    cbv beta iota zeta.
    (* The aux function runs through the ascii list, splits by spaces *)
    reflexivity.
  }

  rewrite Hsplit.
  clear Hsplit input_list.

  (* Filter words with prime length *)

  (* length "This" = 4 (not prime) *)
  (* length "is" = 2 (prime) *)
  (* length "a" = 1 (not prime) *)
  (* length "test" = 4 (not prime) *)

  assert (Hprime_4 : is_prime_bool 4 = false).
  {
    unfold is_prime_bool.
    simpl.
    (* has_divisor_from 4 3 *)
    unfold has_divisor_from.
    cbn.
    (* 4 mod 3 = 1 *)
    (* so continues to has_divisor_from 4 2 *)
    cbn.
    (* 4 mod 2 = 0 -> true *)
    reflexivity.
  }

  assert (Hprime_2 : is_prime_bool 2 = true).
  {
    unfold is_prime_bool.
    simpl.
    (* has_divisor_from 2 1 = false *)
    reflexivity.
  }

  assert (Hprime_1 : is_prime_bool 1 = false) by reflexivity.

  (* Apply filter with these results *)
  unfold List.filter.
  cbn.

  rewrite Hprime_4, Hprime_2, Hprime_1, Hprime_4.
  cbn.

  (* The filtered list is only [list_ascii_of_string "is"] *)
  (* join_words [list_ascii_of_string "is"] = list_ascii_of_string "is" *)
  simpl.

  (* string_of_list_ascii (list_ascii_of_string "is") = "is" by lemma *)
  apply string_list_ascii_inverse.
Qed.