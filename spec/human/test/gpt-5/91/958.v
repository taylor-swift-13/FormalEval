Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

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
  match s with
  | String c1 rest =>
    if Ascii.eqb c1 "I"%char then
      match rest with
      | EmptyString => true
      | String c2 _ => Ascii.eqb c2 " "%char
      end
    else false
  | EmptyString => false
  end.

Definition is_bored_impl (S : string) : nat :=
  let initial := split is_sentence_delimiter S in
  let cleaned := map trim_leading_whitespace initial in
  let boredoms := filter is_boredom_sentence_new cleaned in
  length boredoms.

Definition problem_91_pre (S : string) : Prop := True.

Definition problem_91_spec (S : string) (output : nat) : Prop :=
  output = is_bored_impl S.

Example problem_91_test_long_nat :
  problem_91_spec "WhThe train is always crowded during rush hour. I have to stand the whole wayt to work. Although I live in the suburbs,Yesterday was really busy for me. I had to atvtend three meetings Iand complete a report. n. I love being active! I enjoy visiparksgs to do and see. I especially like visiting the parks and gardens.I wish I could just drive, but parking is too expensive. It is a r.o" 6%nat.
Proof.
  unfold problem_91_spec.
  vm_compute.
  reflexivity.
Qed.

Example problem_91_test_long_Z :
  Z.of_nat (is_bored_impl "WhThe train is always crowded during rush hour. I have to stand the whole wayt to work. Although I live in the suburbs,Yesterday was really busy for me. I had to atvtend three meetings Iand complete a report. n. I love being active! I enjoy visiparksgs to do and see. I especially like visiting the parks and gardens.I wish I could just drive, but parking is too expensive. It is a r.o") = 6%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.