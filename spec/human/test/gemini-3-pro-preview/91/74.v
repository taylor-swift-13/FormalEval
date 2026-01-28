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

Example test_problem_91 : problem_91_spec "The movie we saw last night was really good, but I think I would have enjoyed it more if I had some popThe movie we saw last night was really good,  but I think oI would have enjoyed it  popcorn?corn. Do you like popcorn?" 0.
Proof.
  unfold problem_91_spec.
  unfold is_bored_impl.
  vm_compute.
  reflexivity.
Qed.