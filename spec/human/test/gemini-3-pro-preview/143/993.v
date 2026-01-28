Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* Helper functions for string manipulation *)
Definition list_ascii_of_string (s : string) : list ascii :=
  let fix aux s :=
    match s with
    | EmptyString => []
    | String c s' => c :: aux s'
    end
  in aux s.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

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

(* Changed Fixpoint to Definition as it is not directly recursive (aux is) *)
Definition split_words (s : list ascii) : list (list ascii) :=
  let space := " "%char in
  let fix aux (cur : list ascii) (rest : list ascii) : list (list ascii) :=
    match rest with
    | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
    | h :: t =>
      if Ascii.eqb h space then
        match cur with
        | [] => aux [] t
        | _ => (rev cur) :: aux [] t
        end
      else
        aux (h :: cur) t
    end
  in aux [] s.

Fixpoint join_words (ws : list (list ascii)) : list ascii :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest =>
    w ++ (" "%char :: nil) ++ join_words rest
  end.

Definition words_in_sentence_impl (sentence : string) : string :=
  let words := split_words (list_ascii_of_string sentence) in
  (* Explicitly use List.length to match the type of w : list ascii *)
  let sel := List.filter (fun w => is_prime_bool (List.length w)) words in
  string_of_list_ascii (join_words sel).

Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= List.length l /\ List.length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  output = words_in_sentence_impl sentence.

Example test_problem_143 : problem_143_spec "uithis ittukickesomeowodogs for prime numbersofers ian wodayncek" "for prime ian".
Proof.
  unfold problem_143_spec.
  unfold words_in_sentence_impl.
  (* Compute the function to verify the output matches "for prime ian" *)
  vm_compute.
  reflexivity.
Qed.