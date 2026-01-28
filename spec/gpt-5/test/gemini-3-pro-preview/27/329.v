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
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Fixpoint flip_case_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let n := nat_of_ascii c in
      if Nat.ltb n 128 then
        String (swap_ascii c) (flip_case_utf8 s')
      else
        match s' with
        | EmptyString => String c EmptyString
        | String c2 s'' =>
            let n2 := nat_of_ascii c2 in
            if Nat.eqb n 208 then
               if andb (Nat.leb 144 n2) (Nat.leb n2 159) then
                 String (Ascii.ascii_of_nat 208) (String (Ascii.ascii_of_nat (n2 + 32)) (flip_case_utf8 s''))
               else if andb (Nat.leb 160 n2) (Nat.leb n2 175) then
                 String (Ascii.ascii_of_nat 209) (String (Ascii.ascii_of_nat (n2 - 32)) (flip_case_utf8 s''))
               else if andb (Nat.leb 176 n2) (Nat.leb n2 191) then
                 String (Ascii.ascii_of_nat 208) (String (Ascii.ascii_of_nat (n2 - 32)) (flip_case_utf8 s''))
               else if Nat.eqb n2 129 then
                 String (Ascii.ascii_of_nat 209) (String (Ascii.ascii_of_nat 145) (flip_case_utf8 s''))
               else
                 String c (String c2 (flip_case_utf8 s''))
            else if Nat.eqb n 209 then
               if andb (Nat.leb 128 n2) (Nat.leb n2 143) then
                 String (Ascii.ascii_of_nat 208) (String (Ascii.ascii_of_nat (n2 + 32)) (flip_case_utf8 s''))
               else if Nat.eqb n2 145 then
                 String (Ascii.ascii_of_nat 208) (String (Ascii.ascii_of_nat 129) (flip_case_utf8 s''))
               else
                 String c (String c2 (flip_case_utf8 s''))
            else
               String c (flip_case_utf8 s')
        end
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = flip_case_utf8 s.

Example test_flip_case_cyrillic : flip_case_spec "Карл у аКлары украл кораллы, а Клара у Карлаы украла кланет" "кАРЛ У АкЛАРЫ УКРАЛ КОРАЛЛЫ, А кЛАРА У кАРЛАЫ УКРАЛА КЛАНЕТ".
Proof.
  unfold flip_case_spec.
  simpl.
  reflexivity.
Qed.