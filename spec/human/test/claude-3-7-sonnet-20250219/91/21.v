Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
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
  | String c rest =>
    if is_whitespace c then
      trim_leading_whitespace rest
    else
      s
  | "" => ""
  end.

Definition prefix (p s : string) : bool :=
  let fix pre p s :=
    match p, s with
    | EmptyString, _ => true
    | String c1 p', String c2 s' =>
      if Ascii.eqb c1 c2 then
        pre p' s'
      else
        false
    | _, _ => false
    end
  in pre p s.

Definition is_boredom_sentence_new (s : string) : bool :=
  prefix "I" s.

Definition is_bored_impl (S : string) : nat :=
  let initial := split is_sentence_delimiter S in
  let cleaned := map trim_leading_whitespace initial in
  let boredoms := filter is_boredom_sentence_new cleaned in
  length boredoms.

Definition problem_91_pre (S : string) : Prop := True.

Definition problem_91_spec (S : string) (output : nat) : Prop :=
  output = is_bored_impl S.

Example test_is_bored_complex :
  problem_91_spec
    "I forgot my phone in the car. Oh no, now I have to The movie we saw last night was really good, but I think I would have enjoyed it more if Ip had some popcorn. Do you like popcorn?and get rit."
    1.
Proof.
  unfold problem_91_spec, is_bored_impl, split.
  simpl.
  (* Evaluate split_aux with is_sentence_delimiter on input string yields the list of sentences *)
  (* The string splits on '.', '?', '!' *)
  (* The resulting list (split) is:
     [
       "I forgot my phone in the car";
       " Oh no, now I have to The movie we saw last night was really good, but I think I would have enjoyed it more if Ip had some popcorn";
       " Do you like popcorn";
       "and get rit"
     ]
  *)
  (* Map trim_leading_whitespace to remove leading spaces *)
  (* trimmed list is:
     [
       "I forgot my phone in the car";
       "Oh no, now I have to The movie we saw last night was really good, but I think I would have enjoyed it more if Ip had some popcorn";
       "Do you like popcorn";
       "and get rit"
     ]
  *)
  (* filter sentences starting with "I" *)
  (* Sentence 1: "I forgot my phone in the car" --> starts with 'I' --> keep *)
  (* Sentence 2: "Oh no, now I have to The movie ..." --> starts with 'O' --> discard *)
  (* Sentence 3: "Do you like popcorn" --> starts with 'D' --> discard *)
  (* Sentence 4: "and get rit" --> starts with 'a' --> discard *)
  (* length of filtered is 1 *)
  reflexivity.
Qed.