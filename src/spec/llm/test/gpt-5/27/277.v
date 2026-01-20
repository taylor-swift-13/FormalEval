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

Definition between (n a b : nat) : bool :=
  andb (Nat.leb a n) (Nat.leb n b).

Fixpoint flip_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 s' =>
      let n1 := nat_of_ascii c1 in
      match s' with
      | String c2 s'' =>
          let n2 := nat_of_ascii c2 in
          if andb (Nat.eqb n1 208) (between n2 144 159) then
            String (Ascii.ascii_of_nat 208)
              (String (Ascii.ascii_of_nat (n2 + 32)) (flip_utf8 s''))
          else if andb (Nat.eqb n1 208) (between n2 160 175) then
            String (Ascii.ascii_of_nat 209)
              (String (Ascii.ascii_of_nat (n2 - 32)) (flip_utf8 s''))
          else if andb (Nat.eqb n1 208) (between n2 176 191) then
            String (Ascii.ascii_of_nat 208)
              (String (Ascii.ascii_of_nat (n2 - 32)) (flip_utf8 s''))
          else if andb (Nat.eqb n1 209) (between n2 128 143) then
            String (Ascii.ascii_of_nat 208)
              (String (Ascii.ascii_of_nat (n2 + 32)) (flip_utf8 s''))
          else
            String (swap_ascii c1) (flip_utf8 s')
      | _ => String (swap_ascii c1) (flip_utf8 s')
      end
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_utf8 s.

Example flip_case_mixed: flip_case_spec "BrownКeарл" "bROWNкEАРЛ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.