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

Fixpoint string_rev_utf8_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' =>
    let n := ascii_code c in
    if Nat.eqb n 240 then
      match s' with
      | String c1 s1 =>
        match s1 with
        | String c2 s2 =>
          match s2 with
          | String c3 s3 =>
            string_rev_utf8_aux s3 (String c (String c1 (String c2 (String c3 acc))))
          | _ => string_rev_utf8_aux s2 (String c (String c1 (String c2 acc)))
          end
        | _ => string_rev_utf8_aux s1 (String c (String c1 acc))
        end
      | EmptyString => string_rev_utf8_aux s' (String c acc)
      end
    else string_rev_utf8_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_utf8_aux s EmptyString.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev s.

Example solve_spec_emoji : solve_spec ("😎😂😎😀😂😎"%string) ("😎😂😀😎😂😎"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.