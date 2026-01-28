Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition ascii_eqb (x y : ascii) : bool :=
  match ascii_dec x y with
  | left _ => true
  | right _ => false
  end.

Definition is_delimiter (c : ascii) : bool :=
  if ascii_eqb c ","%char then true
  else if ascii_eqb c " "%char then true
  else Nat.eqb (nat_of_ascii c) 10.

Fixpoint words_string_aux (current_word : list ascii) (input : list ascii) : list (list ascii) :=
  match input with
  | [] => match current_word with [] => [] | _ => [current_word] end
  | c :: cs => if is_delimiter c then
                 match current_word with
                 | [] => words_string_aux [] cs
                 | _ => current_word :: words_string_aux [] cs
                 end
               else words_string_aux (current_word ++ [c]) cs
  end.

Definition words_string_list_impl (s : list ascii) : list (list ascii) :=
  words_string_aux [] s.

Definition words_string (s : string) : list string :=
  map string_of_list_ascii (words_string_list_impl (list_ascii_of_string s)).

Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  output = words_string s.

Example problem_101_test :
  problem_101_spec "President, Joychange,Hi, my space   name   issMulti
line
string
Hello,
world!
paceno John. How     are    ychang e,ou?   ou?hn, F, KennedyThe,quick,brown,fox,jumps,over,the,lazy,dog."%string
    ["President"%string; "Joychange"%string; "Hi"%string; "my"%string; "space"%string; "name"%string; "issMulti"%string; "line"%string; "string"%string; "Hello"%string; "world!"%string; "paceno"%string; "John."%string; "How"%string; "are"%string; "ychang"%string; "e"%string; "ou?"%string; "ou?hn"%string; "F"%string; "KennedyThe"%string; "quick"%string; "brown"%string; "fox"%string; "jumps"%string; "over"%string; "the"%string; "lazy"%string; "dog."%string].
Proof.
  unfold problem_101_spec, words_string, words_string_list_impl.
  vm_compute.
  reflexivity.
Qed.