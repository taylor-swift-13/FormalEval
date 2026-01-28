Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.
Open Scope list_scope.

Definition filter_spaces (l : list ascii) : list ascii :=
  filter (fun c => if ascii_dec c " " then false else true) l.

Definition count_char (letters : list ascii) (c : ascii) : nat :=
  count_occ ascii_dec letters c.

Definition get_max_count (letters : list ascii) : nat :=
  let unique_letters := nodup ascii_dec letters in
  let counts := map (count_char letters) unique_letters in
  fold_right max 0 counts.

Definition problem_111_pre (s : string) : Prop :=
  let letters := list_ascii_of_string s in
  Forall (fun c => c = " " \/ let n := nat_of_ascii c in 97 <= n /\ n <= 122) letters.

Definition problem_111_spec (s : string) (res : list (ascii * nat)) : Prop :=
  let raw_letters := list_ascii_of_string s in
  let letters := filter_spaces raw_letters in
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = []
  | _ :: _ =>
    let max_count := get_max_count letters in
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char letters c = max_count) /\
    (forall c, In c unique_letters ->
      count_char letters c = max_count ->
      In (c, max_count) res)
  end.

Example test_histogram : problem_111_spec "h i j j k l m m m n o o o o  p" [("o", 4)].
Proof.
  unfold problem_111_spec, get_max_count, count_char, filter_spaces.
  split.
  - intros p H.
    destruct H as [H | H]; [ | contradiction ].
    inversion H. subst.
    split; vm_compute; reflexivity.
  - intros c H_in H_count.
    match goal with
    | [ H : In _ ?L |- _ ] =>
      let x := eval vm_compute in L in
      replace L with x in H by (vm_compute; reflexivity)
    end.
    match type of H_count with
    | _ = ?R =>
      let x := eval vm_compute in R in
      replace R with x in H_count by (vm_compute; reflexivity)
    end.
    repeat (destruct H_in as [H_eq | H_in]; [
      subst;
      vm_compute in H_count;
      try discriminate;
      simpl; left; reflexivity
    | ]).
    contradiction.
Qed.