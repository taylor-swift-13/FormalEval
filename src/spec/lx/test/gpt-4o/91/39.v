Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Definition is_sentence_delimiter (c : ascii) : bool :=
  match c with
  | "."%char | "?"%char | "!"%char => true
  | _ => false
  end.

Fixpoint split_aux (p : ascii -> bool) (s : string) (current : string) : list string :=
  match s with
  | "" => [current]
  | String c rest =>
      if p c then
        current :: split_aux p rest ""
      else
        split_aux p rest (current ++ String c "")
  end.

Definition split (p : ascii -> bool) (s : string) : list string :=
  split_aux p s "".

Definition is_whitespace (c : ascii) : bool :=
  match c with
  | " "%char => true
  | _ => false
  end.

Fixpoint trim_leading_whitespace (s : string) : string :=
  match s with
  | String c rest => if is_whitespace c then trim_leading_whitespace rest else s
  | "" => ""
  end.

Definition is_boredom_sentence_new (s : string) : bool :=
  prefix "I " s.

Definition is_bored_spec_new (S : string) (output : nat) : Prop :=
  let initial_sentences := split is_sentence_delimiter S in
  let cleaned_sentences := map trim_leading_whitespace initial_sentences in
  let boredoms := filter is_boredom_sentence_new cleaned_sentences in
  output = length boredoms.

Example is_bored_test_new_case :
  is_bored_spec_new "I am very happy today. I ltoveThe movie we saw last night was really gooThe movie we saw last night was really goodThe movie we staw last night was really good, but I think I would have enjoI am very happy today. I love spending time with my friiends.yed it more if I had some popicorn. Do you like popcorn?, but?d, but I think I would have enjoyed it more if I had some popicorn. oDo you like popcorn? s" 3.
Proof.
  unfold is_bored_spec_new.
  simpl.
  reflexivity.
Qed.