Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_delimiter (c : ascii) : bool :=
  if ascii_dec c ","%char then true
  else if ascii_dec c " "%char then true
  else if ascii_dec c (Ascii.ascii_of_nat 10) then true
  else false.

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
  problem_101_spec
    ("yMulti"%string
     ++ String (Ascii.ascii_of_nat 10) "line!"%string
     ++ String (Ascii.ascii_of_nat 10) "strin!g"%string
     ++ String (Ascii.ascii_of_nat 10) "Hello,i"%string
     ++ String (Ascii.ascii_of_nat 10) "world!"%string
     ++ String (Ascii.ascii_of_nat 10) "?"%string)
    ["yMulti"%string; "line!"%string; "strin!g"%string; "Hello"%string; "i"%string; "world!"%string; "?"%string].
Proof.
  unfold problem_101_spec, words_string, words_string_list_impl.
  vm_compute.
  reflexivity.
Qed.