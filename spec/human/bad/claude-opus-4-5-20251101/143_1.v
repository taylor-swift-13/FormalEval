Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Fixpoint has_divisor_from (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => false
  | S d' =>
    if (n mod d =? 0)%nat then
      true
    else
      has_divisor_from n d'
  end.

Definition is_prime_bool (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => negb (has_divisor_from n (n - 1))
  end.

Fixpoint split_words_aux (cur : list ascii) (rest : list ascii) : list (list ascii) :=
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

Definition split_words (s : list ascii) : list (list ascii) :=
  split_words_aux [] s.

Fixpoint join_words (ws : list (list ascii)) : list ascii :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest =>
    w ++ (" "%char :: nil) ++ join_words rest
  end.

Definition words_in_sentence_impl (sentence : string) : string :=
  let words := split_words (list_ascii_of_string sentence) in
  let sel := filter (fun w => is_prime_bool (length w)) words in
  string_of_list_ascii (join_words sel).

Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= length l /\ length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  output = words_in_sentence_impl sentence.

Example test_words_in_sentence_1 :
  problem_143_spec "This is a test" "is".
Proof.
  unfold problem_143_spec.
  unfold words_in_sentence_impl.
  unfold split_words.
  simpl.
  reflexivity.
Qed.