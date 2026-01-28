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
  prefix "I" s.

Definition is_bored_impl (S : string) : nat :=
  let initial := split is_sentence_delimiter S in
  let cleaned := map trim_leading_whitespace initial in
  let boredoms := filter is_boredom_sentence_new cleaned in
  length boredoms.

Definition problem_91_pre (S : string) : Prop := True.

Definition problem_91_spec (S : string) (output : nat) : Prop :=
  output = is_bored_impl S.

Example problem_91_test_case_nat :
  problem_91_spec "Yesterday was really busy for mehope. nI chad to attend three meetings and complete a Ugh!report.i However, Howcever,yaged to back.go for a run. I love being active!" 1%nat.
Proof.
  unfold problem_91_spec.
  vm_compute.
  reflexivity.
Qed.

Example problem_91_test_case_Z :
  Z.of_nat (is_bored_impl "Yesterday was really busy for mehope. nI chad to attend three meetings and complete a Ugh!report.i However, Howcever,yaged to back.go for a run. I love being active!") = 1%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.