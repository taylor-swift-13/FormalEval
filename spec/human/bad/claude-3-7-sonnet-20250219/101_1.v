Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true | _ => false end.

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

Example test_words_string_Hi_my_name_is_John :
  problem_101_spec "Hi, my name is John" ["Hi"; "my"; "name"; "is"; "John"].
Proof.
  unfold problem_101_spec, words_string.
  unfold words_string_list_impl.
  (* list_ascii_of_string "Hi, my name is John" *)
  replace (list_ascii_of_string "Hi, my name is John")
    with
      ["H"%char; "i"%char; ","%char; " "%char; "m"%char; "y"%char; " "%char;
       "n"%char; "a"%char; "m"%char; "e"%char; " "%char; "i"%char; "s"%char; " "%char;
       "J"%char; "o"%char; "h"%char; "n"%char] by reflexivity.
  simpl.

  (* Compute words_string_aux [] on that list *)
  assert (Hwords :
    words_string_aux []
      ["H"%char; "i"%char; ","%char; " "%char; "m"%char; "y"%char; " "%char;
       "n"%char; "a"%char; "m"%char; "e"%char; " "%char; "i"%char; "s"%char; " "%char;
       "J"%char; "o"%char; "h"%char; "n"%char]
    =
    [["H"%char; "i"%char];
     ["m"%char; "y"%char];
     ["n"%char; "a"%char; "m"%char; "e"%char];
     ["i"%char; "s"%char];
     ["J"%char; "o"%char; "h"%char; "n"%char]]).
  {
    (* Proof by simplification and recursion *)
    revert [].
    generalize
      ["H"%char; "i"%char; ","%char; " "%char; "m"%char; "y"%char; " "%char;
       "n"%char; "a"%char; "m"%char; "e"%char; " "%char; "i"%char; "s"%char; " "%char;
       "J"%char; "o"%char; "h"%char; "n"%char].
    induction l as [| c cs IH]; intros acc.
    - simpl. destruct acc as [| x xs]; simpl; [reflexivity | reflexivity].
    - simpl in *.
      unfold is_delimiter.
      destruct (Ascii.eqb c ","%char) eqn:Ecomma.
      + simpl.
        destruct acc as [| x xs].
        * apply IH.
        * simpl. f_equal. apply IH.
      + destruct (Ascii.eqb c " "%char) eqn:Espace.
        * simpl.
          destruct acc as [| x xs].
          -- apply IH.
          -- simpl. f_equal. apply IH.
        * simpl.
          apply IH.
  }
  rewrite Hwords.
  simpl.
  reflexivity.
Qed.