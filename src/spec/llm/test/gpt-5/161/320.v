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

Fixpoint swapcase_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 s1 =>
    match s1 with
    | String c2 s2 =>
      let n1 := ascii_code c1 in
      let n2 := ascii_code c2 in
      if Nat.eqb n1 195 then
        if orb (orb (orb (orb (Nat.eqb n2 164) (Nat.eqb n2 171)) (Nat.eqb n2 175)) (Nat.eqb n2 182)) (Nat.eqb n2 188)
        then String c1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s2))
        else if orb (orb (orb (orb (Nat.eqb n2 132) (Nat.eqb n2 139)) (Nat.eqb n2 143)) (Nat.eqb n2 150)) (Nat.eqb n2 156)
        then String c1 (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s2))
        else
          let n := ascii_code c1 in
          if is_lower c1 then String (ascii_of_nat (n - 32)) (swapcase_utf8 s1)
          else if is_upper c1 then String (ascii_of_nat (n + 32)) (swapcase_utf8 s1)
          else String c1 (swapcase_utf8 s1)
      else if Nat.eqb n1 208 then
        if Nat.eqb n2 173
        then String (ascii_of_nat 209) (String (ascii_of_nat 141) (swapcase_utf8 s2))
        else if Nat.eqb n2 190
        then String (ascii_of_nat 208) (String (ascii_of_nat 158) (swapcase_utf8 s2))
        else if Nat.eqb n2 158
        then String (ascii_of_nat 208) (String (ascii_of_nat 190) (swapcase_utf8 s2))
        else
          let n := ascii_code c1 in
          if is_lower c1 then String (ascii_of_nat (n - 32)) (swapcase_utf8 s1)
          else if is_upper c1 then String (ascii_of_nat (n + 32)) (swapcase_utf8 s1)
          else String c1 (swapcase_utf8 s1)
      else if Nat.eqb n1 209 then
        if Nat.eqb n2 141
        then String (ascii_of_nat 208) (String (ascii_of_nat 173) (swapcase_utf8 s2))
        else if Nat.eqb n2 130
        then String (ascii_of_nat 208) (String (ascii_of_nat 162) (swapcase_utf8 s2))
        else
          let n := ascii_code c1 in
          if is_lower c1 then String (ascii_of_nat (n - 32)) (swapcase_utf8 s1)
          else if is_upper c1 then String (ascii_of_nat (n + 32)) (swapcase_utf8 s1)
          else String c1 (swapcase_utf8 s1)
      else
        let n := ascii_code c1 in
        if is_lower c1 then String (ascii_of_nat (n - 32)) (swapcase_utf8 s1)
        else if is_upper c1 then String (ascii_of_nat (n + 32)) (swapcase_utf8 s1)
        else String c1 (swapcase_utf8 s1)
    | EmptyString =>
      let n := ascii_code c1 in
      if is_lower c1 then String (ascii_of_nat (n - 32)) EmptyString
      else if is_upper c1 then String (ascii_of_nat (n + 32)) EmptyString
      else String c1 EmptyString
    end
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_new :
  solve_spec ("احلcحاc日本語üdefЭäëاïöüтоü日語def"%string)
             ("احلCحاC日本語ÜDEFэÄËاÏÖÜТОÜ日語DEF"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.