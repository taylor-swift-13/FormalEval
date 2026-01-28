Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Open Scope string_scope.

Definition is_vowel (ch : ascii) : bool :=
  let vowels := ["a"; "e"; "i"; "o"; "u"; "A"; "E"; "I"; "O"; "U"]%char in
  existsb (fun v => Ascii.eqb ch v) vowels.

Definition is_consonant (ch : ascii) : bool :=
  negb (is_vowel ch).

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Definition string_length (s : string) : nat :=
  length (string_to_list s).

Definition nth_char (s : string) (n : nat) : option ascii :=
  nth_error (string_to_list s) n.

Definition valid_vowel_position (word : string) (i : nat) : Prop :=
  let chars := string_to_list word in
  let len := length chars in
  i > 0 /\ i < len - 1 /\
  exists ch_prev ch ch_next,
    nth_error chars (i - 1) = Some ch_prev /\
    nth_error chars i = Some ch /\
    nth_error chars (i + 1) = Some ch_next /\
    is_vowel ch = true /\
    is_consonant ch_prev = true /\
    is_consonant ch_next = true.

Definition no_valid_vowel_after (word : string) (i : nat) : Prop :=
  forall j, j > i -> j < string_length word - 1 -> ~ valid_vowel_position word j.

Definition get_closest_vowel_spec (word : string) (result : string) : Prop :=
  let len := string_length word in
  (len < 3 -> result = EmptyString) /\
  (len >= 3 ->
    (exists i ch,
      valid_vowel_position word i /\
      no_valid_vowel_after word i /\
      nth_char word i = Some ch /\
      result = String ch EmptyString) \/
    ((forall i, ~ valid_vowel_position word i) /\ result = EmptyString)).

Example test_yogurt : get_closest_vowel_spec "yogurt" "u".
Proof.
  unfold get_closest_vowel_spec.
  simpl string_length.
  split.
  - (* Case len < 3 *)
    intros H. lia.
  - (* Case len >= 3 *)
    intros _.
    left.
    exists 3, "u"%char.
    split.
    + (* Prove valid_vowel_position *)
      unfold valid_vowel_position.
      simpl string_to_list. simpl length.
      split.
      * lia. (* 3 > 0 *)
      * split.
        -- lia. (* 3 < 5 *)
        -- (* Provide witnesses: prev='g', curr='u', next='r' *)
           exists "g"%char, "u"%char, "r"%char.
           repeat split.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ vm_compute. reflexivity. (* is_vowel 'u' *)
           ++ vm_compute. reflexivity. (* is_consonant 'g' *)
           ++ vm_compute. reflexivity. (* is_consonant 'r' *)
    + split.
      * (* Prove no_valid_vowel_after *)
        unfold no_valid_vowel_after.
        intros j Hgt Hlt.
        simpl string_length in Hlt.
        (* The only j satisfying 3 < j < 5 is 4 *)
        assert (j = 4) by lia. subst j.
        intro Hvalid.
        unfold valid_vowel_position in Hvalid.
        simpl string_to_list in Hvalid. simpl length in Hvalid.
        destruct Hvalid as (_ & _ & ch_prev & ch & ch_next & Hprev & Hcurr & Hnext & Hv & Hc1 & Hc2).
        (* At index 4, char is 'r' *)
        inversion Hcurr; subst ch.
        (* 'r' is not a vowel *)
        vm_compute in Hv. discriminate.
      * split.
        -- reflexivity.
        -- reflexivity.
Qed.