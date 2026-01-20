Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_nat (n : nat) : bool :=
  andb (Nat.leb 65 n) (Nat.leb n 90).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition is_greek_lower_tail (n : nat) : bool :=
  andb (Nat.leb 177 n) (Nat.leb n 191).

Definition is_greek_upper_tail (n : nat) : bool :=
  andb (Nat.leb 145 n) (Nat.leb n 159).

Fixpoint flip_case (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let n := nat_of_ascii c in
      match s' with
      | String d s'' =>
          let nd := nat_of_ascii d in
          if Nat.eqb n 206 then
            if is_greek_lower_tail nd then
              String c (String (Ascii.ascii_of_nat (nd - 32)) (flip_case s''))
            else if is_greek_upper_tail nd then
              String c (String (Ascii.ascii_of_nat (nd + 32)) (flip_case s''))
            else
              String (swap_ascii c) (flip_case s')
          else
            String (swap_ascii c) (flip_case s')
      | _ =>
          String (swap_ascii c) (flip_case s')
      end
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case s.

Example flip_case_mixed: flip_case_spec "উদাহরQuickষেομαιιএটিμর" "উদাহরqUICKষেΟΜΑΙΙএটিΜর".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.