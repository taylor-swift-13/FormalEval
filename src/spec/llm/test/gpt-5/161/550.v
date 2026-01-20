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

Fixpoint has_letter_utf8 (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c1 s' =>
    let n1 := ascii_code c1 in
    let a1 := is_alpha c1 in
    match s' with
    | EmptyString => a1
    | String c2 s'' =>
      let n2 := ascii_code c2 in
      orb a1
        (if Nat.eqb n1 206
         then if orb (orb (Nat.eqb n2 177) (Nat.eqb n2 178)) (Nat.eqb n2 179) then true
              else if orb (orb (Nat.eqb n2 145) (Nat.eqb n2 146)) (Nat.eqb n2 147) then true
              else has_letter_utf8 s'
         else has_letter_utf8 s')
    end
  end.

Fixpoint swapcase_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 s' =>
    match s' with
    | EmptyString => String (swapcase_char c1) EmptyString
    | String c2 s'' =>
      let n1 := ascii_code c1 in
      let n2 := ascii_code c2 in
      if Nat.eqb n1 206 then
        if orb (orb (Nat.eqb n2 177) (Nat.eqb n2 178)) (Nat.eqb n2 179) then
          String c1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
        else if orb (orb (Nat.eqb n2 145) (Nat.eqb n2 146)) (Nat.eqb n2 147) then
          String c1 (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
        else
          String (swapcase_char c1) (swapcase_utf8 s')
      else
        String (swapcase_char c1) (swapcase_utf8 s')
    end
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter_utf8 s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_unicode : solve_spec ("다γ음버 네이버Αβγ 블로تحويل그"%string) ("다Γ음버 네이버αΒΓ 블로تحويل그"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.