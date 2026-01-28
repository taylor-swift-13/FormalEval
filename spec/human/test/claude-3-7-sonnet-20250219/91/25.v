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

Example test_is_bored_movie :
  problem_91_spec "The movie we saw last night was really good, but?" 0.
Proof.
  unfold problem_91_spec.
  unfold is_bored_impl.
  unfold split.
  simpl.
  (* split_aux splits on '?' producing two parts: "The movie we saw last night was really good, but" and "" *)
  unfold split_aux.
  simpl.
  (* split_aux is called with current = "" and s = full string *)
  (* The first characters are not delimiters until '?' *)
  (* When '?' char is encountered, split_aux returns current :: recursive call with "" *)
  (* For the input, the split_aux will produce: ["The movie we saw last night was really good, but"; ""] *)
  (* trimmed leading whitespace of first string is itself (no leading space) *)
  (* trimmed leading whitespace of second string "" is "" *)
  unfold trim_leading_whitespace.
  simpl.
  (* map trim_leading_whitespace ["The movie we saw last night was really good, but"; ""] is the same list *)
  (* filter is_boredom_sentence_new checks prefix "I" *)
  unfold is_boredom_sentence_new.
  unfold prefix.
  simpl.
  (* prefix "I" "The movie... " returns false since first chars differ *)
  (* prefix "I" "" returns false *)
  (* So filter returns empty list *)
  reflexivity.
Qed.