Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_nat (n : nat) : bool :=
  andb (Nat.leb 65 n) (Nat.leb n 90).

Fixpoint flip_case_aux (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
    let n := nat_of_ascii c in
    if is_lower_nat n then
      String (Ascii.ascii_of_nat (n - 32)) (flip_case_aux s')
    else if is_upper_nat n then
      String (Ascii.ascii_of_nat (n + 32)) (flip_case_aux s')
    else if Nat.eqb n 208 then
      match s' with
      | String c2 s'' =>
        let n2 := nat_of_ascii c2 in
        if andb (Nat.leb 144 n2) (Nat.leb n2 159) then
           String c (String (Ascii.ascii_of_nat (n2 + 32)) (flip_case_aux s''))
        else if andb (Nat.leb 176 n2) (Nat.leb n2 191) then
           String c (String (Ascii.ascii_of_nat (n2 - 32)) (flip_case_aux s''))
        else if andb (Nat.leb 160 n2) (Nat.leb n2 175) then
           String (Ascii.ascii_of_nat 209) (String (Ascii.ascii_of_nat (n2 - 32)) (flip_case_aux s''))
        else
           String c (flip_case_aux s')
      | EmptyString => String c EmptyString
      end
    else if Nat.eqb n 209 then
      match s' with
      | String c2 s'' =>
        let n2 := nat_of_ascii c2 in
        if andb (Nat.leb 128 n2) (Nat.leb n2 143) then
           String (Ascii.ascii_of_nat 208) (String (Ascii.ascii_of_nat (n2 + 32)) (flip_case_aux s''))
        else
           String c (flip_case_aux s')
      | EmptyString => String c EmptyString
      end
    else
      String c (flip_case_aux s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_aux s.

Example test_flip_case_cyrillic : flip_case_spec "Карл у Клары украл кораллы, а К лара у Каарла украла кларнет" "кАРЛ У кЛАРЫ УКРАЛ КОРАЛЛЫ, А к ЛАРА У кААРЛА УКРАЛА КЛАРНЕТ".
Proof.
  unfold flip_case_spec.
  reflexivity.
Qed.