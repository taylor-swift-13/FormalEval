Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Open Scope string_scope.
Open Scope nat_scope.

Definition is_digitb (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 48 n && Nat.leb n 57.

Definition is_upperb (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 65 n && Nat.leb n 90.

Definition is_lowerb (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 97 n && Nat.leb n 122.

Definition is_alphab (c : ascii) : bool := is_upperb c || is_lowerb c.

Fixpoint count_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => if is_digitb c then S (count_digits s') else count_digits s'
  end.

Fixpoint count_char (s : string) (ch : ascii) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => if ascii_dec c ch then S (count_char s' ch) else count_char s' ch
  end.

Definition starts_with_alpha (s : string) : Prop :=
  exists c s', s = String c s' /\ is_alphab c = true.

Definition suffix_in_allowed (suf : string) : Prop :=
  suf = "txt" \/ suf = "exe" \/ suf = "dll".

Definition valid_file_name (s : string) : Prop :=
  count_digits s <= 3 /\
  count_char s (ascii_of_nat 46) = 1 /\
  exists pref suf,
    s = pref ++ String (ascii_of_nat 46) EmptyString ++ suf /\
    pref <> EmptyString /\
    starts_with_alpha pref /\
    suffix_in_allowed suf.

Definition file_name_check_spec (file_name : string) (result : string) : Prop :=
  (valid_file_name file_name /\ result = "Yes") \/
  (~ valid_file_name file_name /\ result = "No").

Example file_name_check_example :
  file_name_check_spec "éxample.exe" "No".
Proof.
  right.
  split.
  - unfold not. intro H.
    unfold valid_file_name in H.
    destruct H as [_ [_ [pref [suf [Hs [Hne [Hstart _]]]]]]].
    destruct pref as [|c0 pref'].
    + contradiction.
    + destruct Hstart as [c [s' [Hpref Halpha]]].
      inversion Hpref; subst c s'.
      assert (forall c1 s1, "éxample.exe" = String c1 s1 -> is_alphab c1 = false) as Hhead_false.
      { intros c1 s1 Heq. inversion Heq. subst. vm_compute. reflexivity. }
      specialize (Hhead_false c0 (pref' ++ String (ascii_of_nat 46) EmptyString ++ suf) Hs).
      rewrite Halpha in Hhead_false. discriminate.
  - reflexivity.
Qed.