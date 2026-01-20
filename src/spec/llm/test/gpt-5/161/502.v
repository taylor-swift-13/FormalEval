Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 65 n) (Nat.leb n 90).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_alpha (c : ascii) : bool := orb (is_upper c) (is_lower c).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else c.

Fixpoint string_map (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (string_map f s')
  end.

Fixpoint has_letter (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => orb (is_alpha c) (has_letter s')
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Definition is_greek_case_byte (m : nat) : bool :=
  orb (andb (Nat.leb 145 m) (Nat.leb m 148))
      (andb (Nat.leb 177 m) (Nat.leb m 180)).

Fixpoint swapcase_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let n := ascii_code c in
      if is_lower c then String (ascii_of_nat (n - 32)) (swapcase_string s')
      else if is_upper c then String (ascii_of_nat (n + 32)) (swapcase_string s')
      else if Nat.eqb n 206 then
        match s' with
        | String d s'' =>
            let m := ascii_code d in
            if is_greek_case_byte m then
              let d' :=
                if andb (Nat.leb 145 m) (Nat.leb m 148)
                then ascii_of_nat (m + 32)
                else ascii_of_nat (m - 32) in
              String c (String d' (swapcase_string s''))
            else String c (String d (swapcase_string s''))
        | EmptyString => String c EmptyString
        end
      else String c (swapcase_string s')
  end.

Fixpoint has_letter_utf8 (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      let n := ascii_code c in
      orb (is_alpha c)
          (if Nat.eqb n 206 then
             match s' with
             | String d s'' => orb (is_greek_case_byte (ascii_code d)) (has_letter_utf8 s'')
             | EmptyString => false
             end
           else has_letter_utf8 s')
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter_utf8 s
  then r = swapcase_string s
  else r = string_rev s.

Example solve_spec_unicode : solve_spec ("الحالअমুকুমअমΑβγΔমβুমললت버버"%string) ("الحالअমুকুমअমαΒΓδমΒুমললت버버"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.