Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

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

Fixpoint split_words (s : list ascii) : list (list ascii) :=
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
  let words : list (list ascii) := split_words (list_ascii_of_string sentence) in
  let sel : list (list ascii) := List.filter (fun (w : list ascii) => is_prime_bool (List.length w)) words in
  string_of_list_ascii (join_words sel).

Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= List.length l /\ List.length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  output = words_in_sentence_impl sentence.

Example problem_143_example_1 :
  problem_143_spec "I am a deveopI Io love eaI love eating pizort aligorithm is efpfIicientting pizzaeloperer" "am deveopI Io eaI is pizzaeloperer".
Proof.
  unfold problem_143_spec.
  vm_compute.
  reflexivity.
Qed.