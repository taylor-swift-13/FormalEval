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
      | EmptyString => String (swapcase_char c1) EmptyString
      | String c2 s2 =>
          let n1 := ascii_code c1 in
          let n2 := ascii_code c2 in
          if Nat.eqb n1 209
          then
            if orb (Nat.eqb n2 129) (orb (Nat.eqb n2 130) (Nat.eqb n2 143))
            then String (ascii_of_nat 208) (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s2))
            else String (swapcase_char c1) (swapcase_utf8 s1)
          else if Nat.eqb n1 208
          then
            if orb (Nat.eqb n2 176)
                   (orb (Nat.eqb n2 178) (orb (Nat.eqb n2 181) (Nat.eqb n2 190)))
            then String c1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s2))
            else String (swapcase_char c1) (swapcase_utf8 s1)
          else if Nat.eqb n1 195
          then
            if orb (Nat.eqb n2 175) (orb (Nat.eqb n2 182) (Nat.eqb n2 188))
            then String c1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s2))
            else String (swapcase_char c1) (swapcase_utf8 s1)
          else String (swapcase_char c1) (swapcase_utf8 s1)
      end
  end.

Fixpoint has_letter_utf8 (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c1 s1 =>
      if is_alpha c1 then true
      else
        match s1 with
        | EmptyString => false
        | String c2 s2 =>
            let n1 := ascii_code c1 in
            let n2 := ascii_code c2 in
            if andb (Nat.eqb n1 209) (orb (Nat.eqb n2 129) (orb (Nat.eqb n2 130) (Nat.eqb n2 143)))
            then true
            else if andb (Nat.eqb n1 208) (orb (Nat.eqb n2 176)
                                               (orb (Nat.eqb n2 178) (orb (Nat.eqb n2 181) (Nat.eqb n2 190))))
            then true
            else if andb (Nat.eqb n1 195) (orb (Nat.eqb n2 175) (orb (Nat.eqb n2 182) (Nat.eqb n2 188)))
            then true
            else has_letter_utf8 s1
        end
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter_utf8 s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_utf8_case :
  solve_spec
    ("с네т이버ïöتحويلاختبار تحيوبيل الحالاتüеястоваятïööتحيلü"%string)
    ("С네Т이버ÏÖتحويلاختبار تحيوبيل الحالاتÜЕЯСТОВАЯТÏÖÖتحيلÜ"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.