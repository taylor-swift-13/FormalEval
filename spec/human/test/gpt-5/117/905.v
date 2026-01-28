Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Example select_words_test_fox_8 :
  select_words ("fox"%string) 8 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example problem_117_spec_test_fox_8Z :
  problem_117_spec ("fox"%string) (Z.to_nat 8%Z) [].
Proof.
  unfold problem_117_spec.
  vm_compute.
  reflexivity.
Qed.