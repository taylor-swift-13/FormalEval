
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Definition is_sentence_delimiter (c : ascii) : bool :=
  match c with
  | "046"%char => true (* . *)
  | "063"%char => true (* ? *)
  | "033"%char => true (* ! *)
  | _ => false
  end.

Definition is_whitespace (c : ascii) : bool :=
  match c with
  | "032"%char => true (* space *)
  | "009"%char => true (* tab *)
  | "010"%char => true (* newline *)
  | "013"%char => true (* carriage return *)
  | _ => false
  end.

Fixpoint split_on_delimiters (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c rest =>
    if is_sentence_delimiter c then
      EmptyString :: split_on_delimiters rest
    else
      match split_on_delimiters rest with
      | [] => [String c EmptyString]
      | h :: t => (String c h) :: t
      end
  end.

Fixpoint strip_leading (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
    if is_whitespace c then strip_leading rest
    else s
  end.

Fixpoint string_reverse_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c rest => string_reverse_aux rest (String c acc)
  end.

Definition string_reverse (s : string) : string :=
  string_reverse_aux s EmptyString.

Definition strip (s : string) : string :=
  string_reverse (strip_leading (string_reverse (strip_leading s))).

Definition starts_with_I_space (s : string) : bool :=
  match s with
  | String "073"%char (String "032"%char _) => true (* "I " *)
  | _ => false
  end.

Definition is_bored_sentence (s : string) : bool :=
  starts_with_I_space (strip s).

Fixpoint count_bored_sentences (sentences : list string) : nat :=
  match sentences with
  | [] => 0
  | h :: t =>
    if is_bored_sentence h then S (count_bored_sentences t)
    else count_bored_sentences t
  end.

Definition is_bored_spec (S : string) (result : nat) : Prop :=
  let sentences := split_on_delimiters S in
  let stripped_sentences := map strip sentences in
  result = count_bored_sentences sentences.
