Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char => true | "e"%char => true | "i"%char => true | "o"%char => true | "u"%char => true
  | "A"%char => true | "E"%char => true | "I"%char => true | "O"%char => true | "U"%char => true
  | _ => false
  end.

Fixpoint count_consonants (w : list ascii) : nat :=
  match w with
  | [] => 0
  | h :: t =>
    let n := nat_of_ascii h in
    let is_upper := (Nat.leb 65 n) && (Nat.leb n 90) in
    let is_lower := (Nat.leb 97 n) && (Nat.leb n 122) in
    let is_letter := is_upper || is_lower in
    (if is_letter && negb (is_vowel h) then 1 else 0) +
    count_consonants t
  end.

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

Definition select_words_impl (s : list ascii) (n : nat) : list (list ascii) :=
  filter (fun w => Nat.eqb (count_consonants w) n) (split_words s).

Definition select_words (s : string) (n : nat) : list string :=
  let l := list_ascii_of_string s in
  let res := select_words_impl l n in
  map string_of_list_ascii res.

Definition problem_117_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_117_spec (s : string) (n : nat) (output : list string) : Prop :=
  output = select_words s n.

Example test_select_words_Mary_little_lamb :
  problem_117_spec "Mary had a little lamb" 4 ["little"].
Proof.
  unfold problem_117_spec, select_words.
  set (lst := list_ascii_of_string "Mary had a little lamb").

  (* Compute split_words lst *)
  remember (split_words lst) as words eqn:Hwords.

  (* Compute split_words lst using vm_compute *)
  (* We do this in a separate assertion to unpack the ascii lists *)
  assert (Hwords_val :
    split_words (list_ascii_of_string "Mary had a little lamb") =
      [ ["M"; "a"; "r"; "y"];
        ["h"; "a"; "d"];
        ["a"];
        ["l"; "i"; "t"; "t"; "l"; "e"];
        ["l"; "a"; "m"; "b"] ]).
  {
    vm_compute. reflexivity.
  }
  rewrite Hwords_val in Hwords.

  (* Now compute select_words_impl lst 4 *)
  unfold select_words_impl.
  rewrite Hwords_val.
  simpl.

  (* Compute count_consonants on each word *)
  assert (count_consonants ["M";"a";"r";"y"] = 3).
  { simpl. reflexivity. }
  assert (count_consonants ["h";"a";"d"] = 2).
  { simpl. reflexivity. }
  assert (count_consonants ["a"] = 0).
  { simpl. reflexivity. }
  assert (count_consonants ["l";"i";"t";"t";"l";"e"] = 4).
  { simpl. reflexivity. }
  assert (count_consonants ["l";"a";"m";"b"] = 3).
  { simpl. reflexivity. }

  (* Filter with Nat.eqb (count_consonants w) 4 *)
  (* Only ["l";"i";"t";"t";"l";"e"] matches *)
  simpl.

  (* Therefore, select_words_impl lst 4 = [["l";"i";"t";"t";"l";"e"]] *)
  (* Finally map string_of_list_ascii over this *)
  simpl.

  reflexivity.
Qed.