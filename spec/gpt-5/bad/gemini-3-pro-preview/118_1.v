Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

(* Specification Definitions *)
Fixpoint nth_char (n : nat) (s : string) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String a s', 0 => Some a
  | String _ s', S n' => nth_char n' s'
  end.

Definition is_vowel (c : ascii) : Prop :=
  c = ascii_of_nat 97 \/
  c = ascii_of_nat 101 \/
  c = ascii_of_nat 105 \/
  c = ascii_of_nat 111 \/
  c = ascii_of_nat 117 \/
  c = ascii_of_nat 65 \/
  c = ascii_of_nat 69 \/
  c = ascii_of_nat 73 \/
  c = ascii_of_nat 79 \/
  c = ascii_of_nat 85.

Definition between_consonants (w : string) (i : nat) (ch : ascii) : Prop :=
  nth_char i w = Some ch /\
  is_vowel ch /\
  (exists a, nth_char (Nat.pred i) w = Some a /\ ~ is_vowel a) /\
  (exists c, nth_char (S i) w = Some c /\ ~ is_vowel c).

Definition get_closest_vowel_spec (word res : string) : Prop :=
  (exists i ch,
      between_consonants word i ch /\
      (forall j, i < j -> forall cj, ~ between_consonants word j cj) /\
      res = String ch EmptyString)
  \/
  ((forall i ch, ~ between_consonants word i ch) /\ res = EmptyString).

(* Helper tactic to solve negation of is_vowel *)
Ltac solve_not_vowel :=
  unfold is_vowel;
  intro H_v;
  cbv in H_v; (* Compute ascii values to expose constructors *)
  repeat destruct H_v as [H_v | H_v];
  inversion H_v. (* Inversion on distinct Ascii values solves the goal *)

(* Proof for the test case *)
Example test_yogurt : get_closest_vowel_spec "yogurt" "u".
Proof.
  unfold get_closest_vowel_spec.
  left.
  (* The vowel 'u' is at index 3 in "yogurt" *)
  exists 3, "u"%char.
  split.
  - (* Prove between_consonants "yogurt" 3 "u" *)
    unfold between_consonants.
    split. { simpl. reflexivity. }
    split.
    + (* is_vowel "u" *)
      unfold is_vowel.
      (* "u" is 117, which is the 5th disjunct *)
      right; right; right; right; left.
      reflexivity.
    + split.
      * (* Preceding character 'g' (index 2) is not a vowel *)
        exists "g"%char.
        split. { simpl. reflexivity. }
        solve_not_vowel.
      * (* Succeeding character 'r' (index 4) is not a vowel *)
        exists "r"%char.
        split. { simpl. reflexivity. }
        solve_not_vowel.

  - split.
    + (* Prove that no index j > 3 satisfies between_consonants *)
      intros j H_gt cj H_bet.
      unfold between_consonants in H_bet.
      destruct H_bet as [H_nth [H_vowel _]].
      
      (* Eliminate cases where j <= 3 *)
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [lia|].
      
      (* Now j represents indices >= 4 *)
      destruct j as [|j].
      * (* Case j = 4: char is 'r' *)
        simpl in H_nth.
        inversion H_nth; subst.
        (* 'r' is not a vowel, contradiction *)
        solve_not_vowel.
        
      * (* Now j represents indices >= 5 *)
        destruct j as [|j].
        -- (* Case j = 5: char is 't' *)
           simpl in H_nth.
           inversion H_nth; subst.
           (* 't' is not a vowel, contradiction *)
           solve_not_vowel.
           
        -- (* Case j >= 6: nth_char returns None *)
           simpl in H_nth.
           discriminate H_nth.

    + (* Result string matches *)
      reflexivity.
Qed.