Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

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
  else match n with
       | 207 => Ascii.ascii_of_nat 206
       | 128 => Ascii.ascii_of_nat 160
       | 129 => Ascii.ascii_of_nat 161
       | 132 => Ascii.ascii_of_nat 164
       | 177 => Ascii.ascii_of_nat 145
       | 181 => Ascii.ascii_of_nat 149
       | 185 => Ascii.ascii_of_nat 153
       | 188 => Ascii.ascii_of_nat 156
       | 173 => Ascii.ascii_of_nat 136
       | 191 => Ascii.ascii_of_nat 159
       | _ => c
       end.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Example test_flip_case_greek : flip_case_spec "πειρατέομαιπειρατέομαι" "ΠΕΙΡΑΤΈΟΜΑΙΠΕΙΡΑΤΈΟΜΑΙ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.